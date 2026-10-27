/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Cech.PushforwardSpectralSequence
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory Limits FiberedCategoryOver.Groupoids
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory Simplicial

universe u

/- Lemma 96.19.11: Let `f : 𝒰 ⟶ 𝒳` and `g : 𝒳 ⟶ 𝒴` be composable 1-morphisms of
categories fibred in groupoids over `(Sch/S)_fppf`. Let
`τ ∈ {Zariski, étale, smooth, syntomic, fppf}`. Assume `F` is an abelian sheaf on
`𝒳_τ`, every object of `𝒳` admits a covering `{xᵢ ⟶ x}` in `𝒳_τ` such that each
`xᵢ` is isomorphic to `f(uᵢ)` for some object of `𝒰`, the category `𝒰` has
equalizers, and the functor `f` is faithful. Then there is a first-quadrant
spectral sequence of abelian sheaves on `𝒴_τ`
`E₁^{p, q} = R^q (g ∘ f_p)_* f_p⁻¹ F ⇒ R^{p+q} g_* F`, where all higher direct
images are computed in the `τ`-topology. -/
@[stacks 072D] #check (AlgebraicGeometry.GroupoidsOver.exists_relativeCechPushforwardSpectralSequence :
  ∀ {S : Scheme.{u}} {U X Y : GroupoidsOver S} (f : U ⟶ X) (g : X ⟶ Y)
    (τ : StandardTopology) (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})
    (hf : coversByEssentialImage f τ)
    [HasEqualizers U.total] [Functor.Faithful (toFunctor f)]
    [HasSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}]
    [HasSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})]
    [∀ p : ℕ, HasSheafify (relativeCechSite f τ p) AddCommGrpCat.{u + 1}]
    [∀ p : ℕ, HasInjectiveResolutions
      (Sheaf (relativeCechSite f τ p) AddCommGrpCat.{u + 1})],
    ∃ (E : CohomologicalSpectralSequenceNat
        (Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}) 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅
          higherDirectImage (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌ ≫ g) τ
            (relativeCechInverseImage f τ F p) q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ higherDirectImage g τ F n))
