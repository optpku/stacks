/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Subalgebra.Directed
public import Mathlib.Algebra.FreeAlgebra.Cardinality
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.159.4

@stack 0GIL

A flat algebra is the filtered union of its flat subalgebras whose cardinality is bounded by
`#A ⊔ ℵ₀`. If the ambient algebra is faithfully flat, every flat subalgebra in this family is
faithfully flat.
-/

open scoped Cardinal

universe u

namespace Subalgebra

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- An `A`-subalgebra of `B` is bounded flat when it is flat over `A` and has cardinality at most
`#A ⊔ ℵ₀`. -/
def IsFlatOfBoundedCardinality (S : Subalgebra A B) : Prop :=
  Module.Flat A S ∧ #S ≤ #A ⊔ ℵ₀

/-- Every bounded-cardinality subalgebra of a flat algebra is contained in a bounded flat
subalgebra. This is the reusable enlargement step behind Lemma 10.159.4. -/
@[stacks 0GIL "bounded flat enlargement"]
theorem exists_flat_bounded_superalgebra [Module.Flat A B] (E : Subalgebra A B)
    (hE : #E ≤ #A ⊔ ℵ₀) :
    ∃ S : Subalgebra A B, E ≤ S ∧ S.IsFlatOfBoundedCardinality := sorry

/-- Lemma 10.159.4 (1): the flat `A`-subalgebras of `B` with cardinality at most `#A ⊔ ℵ₀`
form a directed family under inclusion. -/
@[stacks 0GIL "(1), directed family of bounded flat subalgebras"]
theorem directed_flatSubalgebras_of_boundedCardinality [Module.Flat A B] :
    Directed (· ≤ ·)
      (Subtype.val : {S : Subalgebra A B // S.IsFlatOfBoundedCardinality} → Subalgebra A B) :=
  sorry

/-- Lemma 10.159.4 (2): the bounded flat `A`-subalgebras of `B` cover `B`; equivalently, their
supremum is the top subalgebra. -/
@[stacks 0GIL "(2), bounded flat subalgebras cover the ambient algebra"]
theorem iSup_flatSubalgebras_of_boundedCardinality_eq_top [Module.Flat A B] :
    iSup
        (Subtype.val :
          {S : Subalgebra A B // S.IsFlatOfBoundedCardinality} → Subalgebra A B) =
      (⊤ : Subalgebra A B) := sorry

/-- Lemma 10.159.4 (3): a flat subalgebra of a faithfully flat algebra is faithfully flat over
the base ring. -/
@[stacks 0GIL "(3), faithful flatness of flat subalgebras"]
theorem faithfullyFlat_of_flat [Module.FaithfullyFlat A B] (S : Subalgebra A B)
    [Module.Flat A S] : Module.FaithfullyFlat A S := sorry

@[stacks 0GIL "directed-union support"]
#check @Subalgebra.coe_iSup_of_directed
@[stacks 0GIL "faithful-flatness descent support"]
#check @Module.FaithfullyFlat.of_comap_surjective

end Subalgebra
