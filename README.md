# PigWeedSAT for AgentSAT

An AgentSAT entry: [PigWeedSAT](https://github.com/cscaff/PigWeedSAT), an Amaranth port of the SAT-Accel CDCL
solver (Lo, Chang & Cong, FPGA '25) to the Lattice ECP5-85F, behind the competition's register map (v1).

## How it is put together

| File | What it is |
|---|---|
| `design.py` | The template's register-map shell, unchanged. |
| `solver.py` | The template's `Solver` interface around PigWeedSAT, with an in-hardware loader (below). |
| `pigweed_core.py` | PigWeedSAT's `design.py` (commit `679c136`). One change: `SATAccel` takes its host link as a parameter instead of owning a Wishbone register file, so `design.py`'s `Entry` is the only Wishbone slave. The solver, its kernels and its memories are unchanged. |

PigWeedSAT's original host prepared its memories in Python. Under the register map an entry gets only the
clause stream, so `solver.py` builds the same structures in hardware as the clauses arrive: the paged clause
store, the per-clause records, each literal's chain of occurrence pages (allocated as literals arrive, the way
the solver appends learned clauses), and the initial trail (unit clauses, and variables in no clause). A literal
repeated within a clause is dropped; an empty clause makes the instance UNSAT at once. An instance that does not
fit the stores is REJECTED at start (unsolved, not wrong). After SAT the trail is copied into a per-variable
model RAM that `MODEL_DATA` reads.

Solver settings are PigWeedSAT's recommended ones (`satlat.host.pigweed()`), with 16-word literal pages.

Capacity: 2,048 variables, 8,192 clauses (original plus learned), 12,288 literals. The clause and literal
stores are 16K words each (PigWeedSAT's are 24K): the platform's SoC takes about 53 of the 208 block RAMs,
and at 24K the build needs 233. With 16K stores the whole build uses about 193.

## Testing

`pytest` runs the template's register-map tests. The entry was also run in RTL simulation behind the
competition's own runner and pre-flight (FPSAT `backend/fpsat/rtlsim.py`): edge cases, random formulas checked
against brute force, and the smallest public benchmark instances.

## Credits and licenses

PigWeedSAT is Apache 2.0 (`LICENSE.PigWeedSAT`, `NOTICE`); it reimplements SAT-Accel (Lo, Chang & Cong, FPGA
'25). The register-map shell and template are from the AgentSAT entry template (`LICENSE`, MIT).
