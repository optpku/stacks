/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.7.1

@stack 0563
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 10.7.1: a ring map `φ : R → S` is finite exactly in the canonical sense of
`RingHom.Finite`, namely when the target ring is finite as a module over the source ring. -/
@[stacks 0563 "finite ring map predicate"]
#check @RingHom.Finite

/- Companion recall: for an `R`-algebra `S`, finiteness of the canonical map `algebraMap R S`
is exactly the module-finiteness statement `Module.Finite R S`. -/
@[stacks 0563 "finite algebra-map bridge"]
#check @RingHom.finite_algebraMap
