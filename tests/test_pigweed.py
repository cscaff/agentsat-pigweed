"""The real solver (PigWeedSAT behind solver.py) through the register-map shell, in simulation.

The loader clears its stores after power-up and after every abort (about 4,000 cycles), holding the bus with
wait states meanwhile, as the register map allows; so these transactions wait longer for their ack than the
template's helper does.
"""

from amaranth.sim import Simulator

import design as D
from solver import Solver

START, ABORT = 1, 2
S_BUSY, S_DONE, S_REJ = 1, 2, 4


async def wb(ctx, dut, adr, we=False, data=0, wait=20000):
    ctx.set(dut.wb_adr, adr)
    ctx.set(dut.wb_we, int(we))
    ctx.set(dut.wb_dat_w, data & 0xFFFFFFFF)
    ctx.set(dut.wb_sel, 0xF)
    ctx.set(dut.wb_cyc, 1)
    ctx.set(dut.wb_stb, 1)
    for _ in range(wait):
        await ctx.tick()
        if ctx.get(dut.wb_ack):
            break
    else:
        raise AssertionError(f"no ack for address {adr}")
    value = ctx.get(dut.wb_dat_r)
    await ctx.tick()
    ctx.set(dut.wb_cyc, 0)
    ctx.set(dut.wb_stb, 0)
    await ctx.tick()
    return value


def s32(x):
    return x - (1 << 32) if x & (1 << 31) else x


async def solve(ctx, dut, nvars, clauses):
    await wb(ctx, dut, D.R_CTRL, True, ABORT)
    for _ in range(100):
        if await wb(ctx, dut, D.R_STATUS) == 0:
            break
    await wb(ctx, dut, D.R_NVARS, True, nvars)
    await wb(ctx, dut, D.R_NCLAUSES, True, len(clauses))
    await wb(ctx, dut, D.R_NLITS, True, sum(len(c) for c in clauses))
    for c in clauses:
        for x in c + [0]:
            await wb(ctx, dut, D.R_LOAD, True, x)
    await wb(ctx, dut, D.R_CTRL, True, START)
    for _ in range(5000):
        st = await wb(ctx, dut, D.R_STATUS)
        if st & (S_DONE | S_REJ):
            break
    else:
        raise AssertionError("no answer")
    assert st in (S_DONE, S_REJ)
    if st == S_REJ:
        return "rejected", None
    res = await wb(ctx, dut, D.R_RESULT)
    model = [s32(await wb(ctx, dut, D.R_MODEL)) for _ in range(nvars)] if res == 1 else None
    return res, model


def run(body):
    dut = D.Entry()
    sim = Simulator(dut)
    sim.add_clock(1e-8)
    async def bench(ctx):
        await body(ctx, dut)

    sim.add_testbench(bench)
    sim.run()


def test_capacity_is_declared():
    async def body(ctx, dut):
        assert await wb(ctx, dut, D.R_MAX_VARS) == Solver.max_vars == 2048
        assert await wb(ctx, dut, D.R_MAX_CLAUSES) == Solver.max_clauses == 8192
        assert await wb(ctx, dut, D.R_MAX_LITS) == Solver.max_lits == 12288
    run(body)


def test_sat_with_model_then_unsat_after_abort():
    sat = [[1, 2], [-1, 3], [-3], [2, 2, -1]]          # a repeated literal is dropped
    unsat = [[1, 2], [3, 4], [5, 6], [-1, -3], [-1, -5], [-3, -5], [-2, -4], [-2, -6], [-4, -6]]

    async def body(ctx, dut):
        res, model = await solve(ctx, dut, 3, sat)
        assert res == 1
        assert sorted(abs(x) for x in model) == [1, 2, 3]
        true = {x for x in model if x > 0} | {x for x in model if x < 0}
        assert all(any(x in true for x in c) for c in sat)
        res, model = await solve(ctx, dut, 6, unsat)
        assert res == 2 and model is None
        res, _ = await solve(ctx, dut, 2, [[]])            # an empty clause: UNSAT without solving
        assert res == 2
    run(body)
