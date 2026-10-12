/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.QuasiFinite.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.122.10
@stack 0C6H
-/

universe u v w

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/-! Lemma 10.122.10: quasi-finiteness at a target prime is preserved under
restriction of scalars.  The first recall is the reusable Mathlib-level
predicate; the second includes the finite-type condition in the Stacks
definition. -/

@[stacks 0C6H "quasi-finite-at core"]
#check @Algebra.QuasiFiniteAt.of_restrictScalars

@[stacks 0C6H]
#check @Algebra.FiniteType.QuasiFiniteAt.of_restrictScalars

@[stacks 0C6H "finite-type quasi-finite predicate"]
#check @Algebra.FiniteType.QuasiFiniteAt

@[stacks 0C6H "restriction of scalars for finite type"]
#check @Algebra.FiniteType.of_restrictScalars_finiteType

end
