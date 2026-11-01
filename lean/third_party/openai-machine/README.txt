OpenAI generic bit-program, arithmetic and tape-compiler subset
=============================================================

This independent third-party package supplies concrete finite Boolean-stack
programs and their measured executions. It also supplies a compiler to a
primitive multitape machine with output, time and every-prefix visited-space
preservation. The code and Apache-2.0 license are pinned in UPSTREAM.json.

Entry points
------------
SqrtLogSpace.CompileSpace
  Compile a source trace and a source-stack invariant into a single primitive
  execution with complete output, at most seven steps per source instruction,
  and every-prefix visited-tape space at most s*(B+input.length+15).

ModularRingPrograms
  Fixed-width modular addition and multiplication. wordAdd_value and
  wordMul_value give complete source executions, canonical output widths,
  restored modulus, cleared work stacks and at most 6000*(B+1)^2 instructions.
  Operand words must have length B; the positive modulus has length at most
  B+1 and value at most 2^B. This includes composite moduli.

ModularQuotientPrograms
  quotient_value returns both quotient and remainder with a measured binary
  long-division execution. The supplied divisor must be positive.

ArrayUpdatePrograms
  Reads and replaces fixed-width records in a serialized table. The record
  index is unary; an access costs a linear scan in index times record width.
  These are not constant-time random-access operations.

CounterForPrograms, CounterWidth
  Finite counter-loop compilation and preservation of counter widths.
  Iteration bodies must preserve the stated caller invariant and register /
  stack frame conditions. The program table does not depend on input values.

BitProgramSelectedSpace
  Each source instruction increases the total number of bits on any selected
  set of stacks by at most one. A polynomial-length local call therefore has
  polynomial transient space, including its internal arithmetic temporaries.
  The whole algorithm still needs a persistent-state invariant: applying this
  estimate to its total subexponential running time would not prove polynomial
  space.

ListRegisterProgram, ProgramStateFrames
  Compile fixed word-assignment, append, prepend, head, tail and clear scripts.
  Exact physical executions, alias handling and restoration of the three
  scratch stacks are supplied by the library. The frame rules embed calls
  into arbitrary caller data without re-proving every instruction.

SqrtLogSpace.StructuredSpace
  Compose every-prefix space bounds through calls, sequences, conditionals
  and loops. loop_stack_bound uses a persistent-state invariant and a uniform
  bound for one iteration; its space bound does not grow with the iteration
  count.

All module names above have prefix OAI.Algorithms.SubexponentialSAT.

Provenance and local compatibility
----------------------------------
There are forty-four upstream source files in this dependency package. Some basic
SAT syntax, encoding, polynomial and parameter utilities are included because
the generic implementation imports them. Neither the upstream ETH theorem nor
its SAT counting algorithm is included.

Forty files are byte-for-byte upstream. Four have explicit compatibility
adaptations for Lean 4.33.1: LeanCompat, BitProgramCompile, CounterPrograms and
WeightedSupport. The patch is patches/lean-4.33.1.patch. No executable program,
theorem statement or mathematical definition was changed; the patch narrows
imports, supplies renamed lemma aliases and adjusts proof scripts. The full
upstream lake configuration and unrelated libraries are not imported.

Boundary for this project
-------------------------
TransposeBase/Machine compiles the word language of this project through this
package to the primitive machine, and OnePigeonhole/Machine states the end theorems.
Importing this package alone does not establish them.
