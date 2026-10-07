module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import stacks_project.Chap93.Lemma_93_8_3_Deformation
public import stacks_project.Chap93.Lemma_93_8_8_Henselization

/-!
# Pair henselization as a morphism of deformation categories over C_Λ

The functor `Def_P ⥤ Def_{P^h}` of Lemma 93.8.8, packaged as a based functor
over `ArtinianLocalAlgCat`.
-/

@[expose] public section

open CategoryTheory Functor RingPairCat
open scoped BasedFunctor

universe u

noncomputable section

namespace FlatAlgebraCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (P : Type u) [CommRing P] [Algebra k P]
variable (J : Ideal P)
variable [henselianPairInclusion.IsRightAdjoint]

/-- Pair henselization of deformations commutes with forgetting to `ArtinianLocalAlgCat`. -/
theorem henselizationFunctor_comp_forget :
    henselizationFunctor Λ k P J ⋙
        deformationForget Λ k (henselizationRing (pairOfIdeal J) : Type u) =
      deformationForget Λ k P :=
  sorry

/-- The functor `Def_P ⟶ Def_{P^h}` of Lemma 93.8.8 as a morphism of categories over `C_Λ`. -/
def henselizationBasedFunctor :
    BasedCategory.ofFunctor (deformationForget Λ k P) ⥤ᵇ
      BasedCategory.ofFunctor
        (deformationForget Λ k (henselizationRing (pairOfIdeal J) : Type u)) where
  toFunctor := henselizationFunctor Λ k P J
  w := henselizationFunctor_comp_forget Λ k P J

/-- The underlying functor of `henselizationBasedFunctor` is `henselizationFunctor`. -/
theorem henselizationBasedFunctor_toFunctor :
    (henselizationBasedFunctor Λ k P J).toFunctor = henselizationFunctor Λ k P J :=
  sorry

end FlatAlgebraCat

end
