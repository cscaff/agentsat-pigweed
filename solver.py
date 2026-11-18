"""PigWeedSAT behind the AgentSAT register map.

`design.py` (the template's register-map shell, unchanged) drives `Solver` through the interface described
there: sizes, a stream of clause words, start and abort; it reads back done/result and the model one variable
at a time. PigWeedSAT (`pigweed_core.py`) is a CDCL solver whose original host prepared its memories in Python
before a run. Here that preparation happens in hardware, as the clauses stream in, so the entry needs no host
code:

  clause store     each clause's literals, 3 per 4-word page, slot 3 the next page (0 on the last); unused
                   slots written 0
  clause records   cmd = (first page, length), cst = (XOR of the literals, length)
  literal store    for every literal, a chain of P-word pages listing the clauses (id + 1) that contain it;
                   slot P-2 the previous page, slot P-1 the next. Pages are allocated as literals arrive,
                   exactly as the solver itself appends learned clauses, and zeroed first (RAM keeps the
                   previous instance's contents; abort does not clear it)
  initial trail    every unit clause's literal (once), and +v for each variable that appears in no clause
  duplicates       a literal repeated within a clause is dropped (as the original host did); a clause with
                   both v and -v is kept
  empty clause     the instance is UNSAT; reported without running the solver

Anything that does not fit (clause store, literal store, clause ids, clause length, trail) sets an overflow
flag; the instance is then REJECTED at start, which counts as unsolved, never wrong.

After a SAT result the solver's trail (the answer stack) is copied into a one-bit-per-variable model RAM,
which `model_val` reads with one cycle of latency. Results: solver 1 -> SAT, 0 -> UNSAT, a negative code
(the solver ran out of memory, for example) -> unknown, with the code in `info`.

The solver runs with PigWeedSAT's heuristics (`satlat.host.pigweed()`): memory-pressure restarts at 256 free
clause pages / 32 free literal pages, glue clauses kept, used clauses spared once, abstract-level
minimization; literal pages of 16 words, as in the October runs on the lab boards.
"""

from amaranth import Cat, Elaboratable, Module, Mux, ResetInserter, Signal, Value, signed
from amaranth.lib.memory import Memory

import pigweed_core as P
from pigweed_core import (C_MAX, CA_W, CE_MAX, CID_W, CS_W, LA_W, LE_MAX, LIT_W, N_MAX, NUM_W, VAR_W,
                          L_CMD, L_CST, L_OCC, SATAccel, _Ports, fit, pack)

LIT_PAGE = 16                       # literal-store page size P (a power of two)
FREE_INIT = LIT_PAGE - 3            # free slots after the first entry of a fresh page
FREE_EMPTY = LIT_PAGE - 2           # free slots of an empty page
INFO_OVERFLOW = 0x0F0               # REJECTED: the instance did not fit (read from INFO)


def occ_index(v, side):
    """Occurrence-list index of (variable, side): 2 * v + side (side 0 positive, 1 negative)."""
    return Cat(side, fit(v, VAR_W))


def stamp_word(tag, pos, neg, upos, uneg):
    """A variable's stamp: the clause it was last seen in (id + 1), the signs seen there, and whether each
    sign has been put on the trail as a unit."""
    return Cat(fit(tag, CID_W), pos, neg, upos, uneg)


class StreamHost(Elaboratable):
    """The solver's host link: builds PigWeedSAT's memories from the clause stream, starts it, and serves the
    model. Takes the place of pigweed_core.HostInterface (same idle/go/abort contract)."""

    def __init__(self, sv, cfg, mems, status):
        self.sv, self.cfg, self.status = sv, cfg, status
        # meta is borrowed while loading (the stamps below); the solver rewrites all of it in its INIT
        self.p = _Ports(mems, "host", "ls", "cs", "cmd", "cst", "occ", "stk", "meta")
        self.idle = Signal()     # input: the solver is idle, its memories are ours
        self.go = Signal()       # output: start the solver
        self.abort = Signal()    # output: reset the solver

    def elaborate(self, platform):  # noqa: C901
        m = Module()
        sv, cfg, p, st = self.sv, self.cfg, self.p, self.status

        # Per-variable stamps (duplicate and unit tracking) live in the solver's `meta` RAM while loading: it
        # is idle then, and the solver's INIT rewrites every entry before it is used, so this costs no block
        # RAM (a separate stamp memory would need two of the 208, and the design has none to spare).
        class _StampRead:
            def __init__(self, port):
                self.port = port
                self.data = Value.cast(port.rdata)
                self.addr = port.raddr

        class _StampWrite:
            def __init__(self, port):
                self.addr, self.en = port.waddr, port.we
                self.data = port.wdata

        sr, sw = _StampRead(p.meta), _StampWrite(p.meta)
        # the model: one bit per variable, in LUT RAM
        m.submodules.model = model = Memory(shape=1, depth=N_MAX, init=[],
                                            attrs={"ram_style": "distributed"})
        mw, mr = model.write_port(), model.read_port()

        # the model is readable whenever the shell asks (it only asks after a SAT result)
        m.d.comb += [mr.addr.eq(sv.model_addr[:VAR_W]), sv.model_val.eq(mr.data)]

        i = Signal(LA_W + 2)                 # clear / finalize / copy counter
        cs_ptr = Signal(CA_W + 2)
        ls_ptr = Signal(LA_W + 2)
        cls = Signal(CID_W + 1)              # clauses kept so far (index of the current one)
        cls_start = Signal(CA_W + 2)
        cnt = Signal(NUM_W + 1)              # literals kept in the current clause
        xor = Signal(signed(32))
        lit = Signal(signed(32))
        last_lit = Signal(signed(32))
        var = Signal(VAR_W + 1)
        fixed = Signal(VAR_W + 2)            # initial trail length
        overflow = Signal()
        empty = Signal()
        start_pending = Signal()
        o = Signal(L_OCC)                    # the occurrence record being extended
        side = Signal()
        nopage = Signal()
        np_ = Signal(LA_W + 2)               # a new literal-store page
        z = Signal(range(LIT_PAGE + 1))
        pos_o = Signal(L_OCC)                # finalize: a variable's two lists
        neg_o = Signal(L_OCC)
        result = Signal(2)
        info = Signal(32)
        height = Signal(VAR_W + 2)

        cid = (cls + 1)[:CID_W]
        st_tag = sr.data[:CID_W]
        st_pos, st_neg = sr.data[CID_W], sr.data[CID_W + 1]
        st_upos, st_uneg = sr.data[CID_W + 2], sr.data[CID_W + 3]

        with m.If(sv.start):                 # a start can come while the stores are still being cleared
            m.d.sync += start_pending.eq(1)

        m.d.comb += [self.abort.eq(sv.abort), sv.result.eq(result), sv.info.eq(info)]

        with m.FSM(name="loader"):
            # -------------------------------------------------- clear (after power-up and every abort)
            with m.State("CLEAR"):
                m.d.comb += sv.idle.eq(1)
                with m.If(i == 2 * N_MAX):
                    m.d.sync += [i.eq(0), cs_ptr.eq(0), ls_ptr.eq(0), cls.eq(0), cls_start.eq(0),
                                 cnt.eq(0), xor.eq(0), fixed.eq(0), overflow.eq(0), empty.eq(0)]
                    m.next = "READY"
                with m.Else():
                    p.occ.write(m, i, 0)
                    with m.If(i < N_MAX):
                        p.meta.write(m, i, 0)
                    m.d.sync += i.eq(i + 1)

            # -------------------------------------------------- the clause stream
            with m.State("READY"):
                m.d.comb += [sv.idle.eq(1), sv.load_ready.eq(1)]
                d = sv.load_data
                a = Mux(d < 0, -d, d)
                with m.If(sv.start | start_pending):
                    m.d.sync += [start_pending.eq(0), i.eq(0)]
                    m.next = "FIN"
                with m.Elif(sv.load_valid):
                    m.d.sync += [lit.eq(d), var.eq((a - 1)[:VAR_W + 1])]
                    with m.If(d == 0):
                        m.next = "END"
                    with m.Elif(overflow | (a > N_MAX) | (a > sv.nvars)):
                        m.d.sync += overflow.eq(1)        # keep taking the stream, then reject
                    with m.Else():
                        m.d.comb += sr.addr.eq((a - 1)[:VAR_W])
                        m.next = "LIT"

            with m.State("LIT"):                          # stamp read back: a repeat within this clause?
                is_pos = lit > 0
                seen_here = st_tag == cid
                dup = seen_here & Mux(is_pos, st_pos, st_neg)
                with m.If(dup):
                    m.next = "READY"
                with m.Elif((cs_ptr + 2 > CE_MAX) | (cnt == (1 << NUM_W) - 1)):
                    m.d.sync += overflow.eq(1)
                    m.next = "READY"
                with m.Else():
                    keep_pos = Mux(seen_here, st_pos, 0) | is_pos
                    keep_neg = Mux(seen_here, st_neg, 0) | ~is_pos
                    m.d.comb += [sw.addr.eq(var[:VAR_W]), sw.en.eq(1),
                                 sw.data.eq(stamp_word(cid, keep_pos, keep_neg, st_upos, st_uneg))]
                    with m.If(cs_ptr[:2] == 3):           # this clause page is full: link the next one
                        p.cs.write(m, cs_ptr, cs_ptr + 1)
                        m.d.sync += cs_ptr.eq(cs_ptr + 1)
                    m.d.sync += side.eq(~is_pos)
                    m.next = "LIT_W"

            with m.State("LIT_W"):                        # the literal into the clause store
                p.cs.write(m, cs_ptr, lit[:CS_W])
                p.occ.read(m, occ_index(var, side))
                m.d.sync += [cs_ptr.eq(cs_ptr + 1), xor.eq(xor ^ lit), cnt.eq(cnt + 1), last_lit.eq(lit)]
                m.next = "OCC"

            with m.State("OCC"):                          # add this clause to the literal's list
                rec = p.occ.rdata
                fresh = (rec.num == 0) & (rec.free == 0)
                m.d.sync += [o.eq(rec), nopage.eq(fresh)]
                with m.If(fresh | (rec.free == 0)):
                    with m.If(ls_ptr + LIT_PAGE > LE_MAX):
                        m.d.sync += overflow.eq(1)
                        m.next = "READY"
                    with m.Else():
                        m.d.sync += [np_.eq(ls_ptr), z.eq(0)]
                        m.next = "ZERO"
                with m.Else():
                    p.ls.write(m, rec.latest + (LIT_PAGE - 2) - rec.free, cid)
                    p.occ.write(m, occ_index(var, side), pack(L_OCC, start=rec.start, latest=rec.latest,
                                                              num=rec.num + 1, free=rec.free - 1))
                    m.next = "READY"

            with m.State("ZERO"):                         # a fresh page, zeroed
                with m.If(z == LIT_PAGE):
                    m.next = "LINK0"
                with m.Else():
                    p.ls.write(m, np_ + z, 0)
                    m.d.sync += z.eq(z + 1)

            with m.State("LINK0"):
                p.ls.write(m, np_, cid)
                p.occ.write(m, occ_index(var, side), pack(L_OCC, start=Mux(nopage, np_, o.start), latest=np_,
                                                          num=o.num + 1, free=FREE_INIT))
                m.d.sync += ls_ptr.eq(ls_ptr + LIT_PAGE)
                with m.If(nopage):
                    m.next = "READY"
                with m.Else():
                    m.next = "LINK1"
            with m.State("LINK1"):                        # the new page's previous-page slot
                p.ls.write(m, np_ + LIT_PAGE - 2, o.latest)
                m.next = "LINK2"
            with m.State("LINK2"):                        # the old page's next-page slot
                p.ls.write(m, o.latest + LIT_PAGE - 1, np_)
                m.next = "READY"

            # -------------------------------------------------- end of a clause
            with m.State("END"):
                with m.If(cnt == 0):
                    m.d.sync += empty.eq(1)               # an empty clause: the instance is UNSAT
                    m.next = "READY"
                with m.Elif(overflow):
                    m.next = "NEXT"
                with m.Elif(cs_ptr[:2] != 0):             # pad the last page (and its next slot) with 0
                    p.cs.write(m, cs_ptr, 0)
                    m.d.sync += cs_ptr.eq(cs_ptr + 1)
                with m.Elif(cls >= C_MAX):
                    m.d.sync += overflow.eq(1)
                    m.next = "NEXT"
                with m.Else():
                    p.cmd.write(m, cls, pack(L_CMD, start=cls_start, num=cnt))
                    m.next = "END_CST"
            with m.State("END_CST"):
                p.cst.write(m, cls, pack(L_CST, comp=xor, rem=cnt))
                with m.If(cnt == 1):
                    m.d.comb += sr.addr.eq(P.var_of(last_lit))
                    m.next = "UNIT"
                with m.Else():
                    m.next = "NEXT"
            with m.State("UNIT"):                         # a unit clause: its literal joins the trail, once
                is_pos = last_lit > 0
                already = Mux(is_pos, st_upos, st_uneg)
                with m.If(~already):
                    with m.If(fixed >= N_MAX):
                        m.d.sync += overflow.eq(1)
                    with m.Else():
                        p.stk.write(m, fixed, last_lit[:LIT_W])
                        m.d.sync += fixed.eq(fixed + 1)
                        m.d.comb += [sw.addr.eq(P.var_of(last_lit)), sw.en.eq(1),
                                     sw.data.eq(stamp_word(st_tag, st_pos, st_neg,
                                                           st_upos | is_pos, st_uneg | ~is_pos))]
                m.next = "NEXT"
            with m.State("NEXT"):
                m.d.sync += [cls.eq(cls + 1), cnt.eq(0), xor.eq(0), cls_start.eq(cs_ptr)]
                m.next = "READY"

            # -------------------------------------------------- start: finish the layout, then solve
            with m.State("FIN"):
                with m.If(overflow):
                    m.d.sync += info.eq(INFO_OVERFLOW)
                    m.next = "REJECT"
                with m.Elif(empty):
                    m.d.sync += [result.eq(2), info.eq(0)]
                    m.next = "DONE"
                with m.Elif(i == sv.nvars):
                    m.next = "CFG"
                with m.Else():
                    p.occ.read(m, occ_index(i, 0))
                    m.next = "FIN_POS"
            with m.State("FIN_POS"):
                m.d.sync += pos_o.eq(p.occ.rdata)
                p.occ.read(m, occ_index(i, 1))
                m.next = "FIN_NEG"
            with m.State("FIN_NEG"):
                m.d.sync += neg_o.eq(p.occ.rdata)
                m.next = "FIN_V"
            with m.State("FIN_V"):
                pe = (pos_o.num == 0) & (pos_o.free == 0)
                ne = (neg_o.num == 0) & (neg_o.free == 0)
                with m.If(pe & ne):                       # in no clause: fixed true, no pages
                    with m.If(fixed >= N_MAX):
                        m.d.sync += overflow.eq(1)
                        m.next = "FIN"
                    with m.Else():
                        p.occ.write(m, occ_index(i, 0), pack(L_OCC, start=ls_ptr, latest=ls_ptr, num=0, free=0))
                        p.stk.write(m, fixed, (i + 1)[:LIT_W])
                        m.d.sync += fixed.eq(fixed + 1)
                        m.next = "FIN_UNUSED"
                with m.Elif(pe | ne):                     # one side in no clause: it still gets an empty page
                    with m.If(ls_ptr + LIT_PAGE > LE_MAX):
                        m.d.sync += overflow.eq(1)
                        m.next = "FIN"
                    with m.Else():
                        m.d.sync += [side.eq(ne), np_.eq(ls_ptr), z.eq(0)]
                        m.next = "FIN_ZERO"
                with m.Else():
                    m.d.sync += i.eq(i + 1)
                    m.next = "FIN"
            with m.State("FIN_UNUSED"):
                p.occ.write(m, occ_index(i, 1), pack(L_OCC, start=ls_ptr, latest=ls_ptr, num=0, free=0))
                m.d.sync += i.eq(i + 1)
                m.next = "FIN"
            with m.State("FIN_ZERO"):
                with m.If(z == LIT_PAGE):
                    p.occ.write(m, occ_index(i, side), pack(L_OCC, start=np_, latest=np_, num=0, free=FREE_EMPTY))
                    m.d.sync += [ls_ptr.eq(ls_ptr + LIT_PAGE), i.eq(i + 1)]
                    m.next = "FIN"
                with m.Else():
                    p.ls.write(m, np_ + z, 0)
                    m.d.sync += z.eq(z + 1)

            with m.State("CFG"):
                m.d.sync += [
                    cfg.n_vars.eq(sv.nvars), cfg.n_cls.eq(cls), cfg.lit_elems.eq(ls_ptr),
                    cfg.cls_elems.eq(cs_ptr), cfg.fixed_init.eq(fixed), cfg.pos_phase.eq(0),
                    cfg.P.eq(LIT_PAGE), cfg.reset_mult.eq(100), cfg.prune_q16.eq(6553),
                    cfg.low_cp.eq(256), cfg.low_lp.eq(32), cfg.glue.eq(1),
                    cfg.hflags.eq(0b11), cfg.rephase.eq(0),
                ]
                m.next = "GO"
            with m.State("GO"):
                m.d.comb += self.go.eq(1)
                m.next = "RUN"
            with m.State("RUN"):
                r = st["result"]
                with m.If(self.idle & st["done"]):
                    m.d.sync += height.eq(st["height"])
                    with m.If(r == 1):
                        m.d.sync += [result.eq(1), info.eq(0), i.eq(0)]
                        m.next = "COPY"
                    with m.Elif(r == 0):
                        m.d.sync += [result.eq(2), info.eq(0)]
                        m.next = "DONE"
                    with m.Else():
                        m.d.sync += [result.eq(0), info.eq(r)]
                        m.next = "DONE"

            # -------------------------------------------------- SAT: trail -> model
            with m.State("COPY"):
                with m.If(i == height):
                    m.next = "DONE"
                with m.Else():
                    p.stk.read(m, i)
                    m.next = "COPY_W"
            with m.State("COPY_W"):
                t = p.stk.rdata
                m.d.comb += [mw.addr.eq(P.var_of(t)), mw.data.eq(t > 0), mw.en.eq(1)]
                m.d.sync += i.eq(i + 1)
                m.next = "COPY"

            with m.State("DONE"):
                m.d.comb += sv.done.eq(1)
            with m.State("REJECT"):
                m.d.comb += sv.rejected.eq(1)

        # abort: drop everything and clear again (the solver core resets itself on the same signal)
        return ResetInserter({"sync": sv.abort})(m)


class Solver(Elaboratable):
    # Largest instance PigWeedSAT can hold (pigweed_core's N_MAX, C_MAX, and the clause store's 3 literals
    # per 4-word page). An instance within these that still does not fit is REJECTED (unsolved, not wrong).
    max_vars = N_MAX
    max_clauses = C_MAX
    max_lits = CE_MAX * 3 // 4

    def __init__(self):
        # From the shell.
        self.start = Signal()
        self.abort = Signal()
        self.nvars = Signal(32)
        self.nclauses = Signal(32)
        self.nlits = Signal(32)
        self.load_valid = Signal()
        self.load_data = Signal(signed(32))
        self.model_addr = Signal(32)
        # To the shell.
        self.idle = Signal()
        self.load_ready = Signal()
        self.done = Signal()
        self.rejected = Signal()
        self.result = Signal(2)
        self.info = Signal(32)
        self.model_val = Signal()

    def elaborate(self, platform):
        m = Module()
        m.submodules.pigweed = SATAccel(lambda cfg, mems, status: StreamHost(self, cfg, mems, status))
        return m
