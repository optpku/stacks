/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Cech.SpectralSequence
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory Limits FiberedCategoryOver.Groupoids
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory Simplicial

universe u

/- Lemma 96.19.8: Let `f : 𝒰 ⟶ 𝒳` be a 1-morphism of categories fibred in groupoids
over `(Sch/S)_fppf`. Let `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`. Assume `F` is
an abelian sheaf on `𝒳_τ`, every object of `𝒳` admits a covering `{xᵢ ⟶ x}` in `𝒳_τ`
such that each `xᵢ` is isomorphic to `f(uᵢ)` for some object of `𝒰`, the category `𝒰`
has equalizers, and the functor `f` is faithful. Then there is a first-quadrant spectral
sequence of abelian groups `E₁^{p, q} = H^q((𝒰_p)_τ, f_p⁻¹ F) ⇒ H^{p+q}(𝒳_τ, F)`
converging to the cohomology of `F` in the `τ`-topology. -/
@[stacks 06XF] #check (AlgebraicGeometry.GroupoidsOver.exists_relativeCechSpectralSequence :
  ∀ {S : Scheme.{u}} {U X : GroupoidsOver S} (f : U ⟶ X) (τ : StandardTopology)
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})
    (hf : coversByEssentialImage f τ)
    [HasEqualizers U.total] [Functor.Faithful (toFunctor f)]
    [HasSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})]
    [∀ p : ℕ, HasSheafify (relativeCechSite f τ p) AddCommGrpCat.{u + 1}]
    [∀ p : ℕ, HasExt.{u + 1} (Sheaf (relativeCechSite f τ p) AddCommGrpCat.{u + 1})],
    ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{u + 1} 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅ relativeCechPageOne f τ F p q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ (Sheaf.functorH (X.associatedTopology τ) n).obj F))
