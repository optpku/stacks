module

import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Finite
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 30.13.1: let `f : Y ⟶ X` be finite and surjective with `X` locally Noetherian, and
let `Z ⊆ X` be an integral closed subscheme with generic point `ξ`. There exists a coherent
`𝒪_Y`-module `ℱ` such that `Supp(f_* ℱ) = Z` as a subset of `X`, and the stalk
`(f_* ℱ)_ξ` is annihilated by the maximal ideal `𝔪_ξ`. -/
@[stacks 01YO] #check (
  AlgebraicGeometry.Scheme.Modules.exists_coherent_pushforward_support_eq_and_stalk_annihilated :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Surjective f] [IsLocallyNoetherian X]
      (Z : X.IdealSheafData) [IsIntegral Z.subscheme]
      (ξ : X) (hξ : IsGenericPoint ξ (Z.support : Set X)),
      ∃ ℱ : Y.Modules,
        ∃ _ : ℱ.IsCoherent,
          ∃ _ : RingedSpace.moduleSupport ((Scheme.Modules.pushforward f).obj ℱ) =
              (Z.support : Set X),
            ∀ r : X.presheaf.stalk ξ,
              r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) →
                ∀ m : RingedSpace.stalkModuleCat ((Scheme.Modules.pushforward f).obj ℱ) ξ,
                  r • m = 0)
