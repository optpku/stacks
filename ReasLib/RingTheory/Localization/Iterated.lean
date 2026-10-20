module

public import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Iterated localizations at two submonoids

@stack 02C6

This file names the canonical equivalence between localization at a supremum and localization
in two stages. The underlying localization predicate and uniqueness equivalence are provided by
Mathlib.
-/

@[expose] public section

noncomputable section

universe u

namespace Localization

variable {A : Type u} [CommRing A]

/-- Proposition 10.9.10: localization at the supremum of two denominator submonoids is
canonically equivalent to first localizing at `S'` and then at the image of `S`. -/
@[stacks 02C6 "iterated localization equivalence"]
noncomputable def supEquivIterated (S S' : Submonoid A) :
    Localization (S ⊔ S') ≃ₐ[A]
      Localization (Algebra.algebraMapSubmonoid (Localization S') S) := by
  haveI : IsLocalization (S ⊔ S')
      (Localization (Algebra.algebraMapSubmonoid (Localization S') S)) := by
    sorry
  exact IsLocalization.algEquiv (S ⊔ S') _ _

/-- The iterated-localization equivalence agrees with the canonical maps from the base ring. -/
@[simp, stacks 02C6 "iterated localization equivalence on scalars"]
theorem supEquivIterated_apply_algebraMap (S S' : Submonoid A) (a : A) :
    supEquivIterated S S' (algebraMap A _ a) = algebraMap A _ a := sorry

/-- The canonical equivalence sends `a / (s * s')` to the iterated fraction
`(a / s') / (s / 1)`. -/
@[stacks 02C6 "iterated localization equivalence on fractions"]
theorem supEquivIterated_mk (S S' : Submonoid A) (a : A) (s : S) (s' : S') :
    supEquivIterated S S'
      (Localization.mk a
        ⟨s * s', Submonoid.mul_mem_sup s.property s'.property⟩) =
      Localization.mk (Localization.mk a s')
        ⟨algebraMap A (Localization S') s, Algebra.mem_algebraMapSubmonoid_of_mem s⟩ := sorry

end Localization
