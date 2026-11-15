"""Your solver goes here.

`design.py` implements the FPSAT register map (docs/register_map_v1.md) and
talks to this module through the small interface below. Replace the body of
`Solver.elaborate` with your design and keep the ports, the class name and the
capacity constants. You can add other files, import them here, and list them in
`info.yaml`.

The placeholder below gives up on every instance: it reports DONE with result
UNKNOWN as soon as it is started. That is a legal answer, so the template runs
through the whole pipeline as is, and scores 2T on every instance.

Interface (all signals are in the `sync` domain, which is your design clock):

Driven by the shell (inputs to you):
    start        1-cycle pulse. A new instance begins. The sizes below are valid.
    abort        level. While high you MUST drop all instance state. See `idle`.
    nvars, nclauses, nlits
                 the instance size from the DIMACS header and the literal count
                 (not counting the 0 terminators). Stable from before `start`
                 until the next abort.
    load_valid   1-cycle strobe: `load_data` carries one word of the clause
                 stream. A positive or negative literal, or 0 to end a clause.
                 The shell only strobes when `load_ready` is high.
    load_data    signed 32-bit word.
    model_addr   0-based variable index to read the model for (variable
                 model_addr + 1). Held stable while the shell reads a literal.

Driven by you (outputs):
    idle         high when you hold no instance state and can take a new
                 instance. Must be high at power-up. After `abort` goes high
                 it must go high within 1,000 cycles. The runner waits for it.
    load_ready   high when you can accept a `load_valid` strobe. Hold it low to
                 stall the clause stream.
    done         high (a 1-cycle pulse is enough) when the solve has finished
                 and `result` is valid. Only used while an instance is running.
    rejected     high (a pulse is enough) if you find you cannot hold this
                 instance. It counts as unsolved, not wrong.
    result       0 unknown, 1 SAT, 2 UNSAT. Sampled on `done`.
    info         optional 32-bit reason code, for logs only. Sampled on `done`.
    model_val    the value of variable `model_addr + 1` in the model: 1 true,
                 0 false. It is read one cycle AFTER `model_addr`, so a block
                 RAM with a registered output works. Only read after a SAT
                 result.

Capacity: declare the largest instance you can hold below. The runner skips any
instance that is larger, and counts it as unsolved. Do not declare more than
you can hold: a wrong answer is worse than a skip. The placeholder holds
nothing, so all three are 0. Change them once your solver works.
"""

from amaranth import Elaboratable, Module, Signal, signed


class Solver(Elaboratable):
    # Largest instance you can hold. Set these honestly.
    max_vars = 0
    max_clauses = 0
    max_lits = 0

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

        # TODO: replace this placeholder with your solver.
        m.d.comb += [
            self.idle.eq(1),
            self.load_ready.eq(1),
            self.result.eq(0),  # unknown: give up
            self.info.eq(0),
        ]
        m.d.sync += self.done.eq(self.start)

        return m
