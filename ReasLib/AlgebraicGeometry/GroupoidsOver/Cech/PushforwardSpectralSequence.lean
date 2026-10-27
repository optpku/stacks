/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Cech.SpectralSequence
public import ReasLib.AlgebraicGeometry.GroupoidsOver.HigherDirectImage

/-!
# The relative Čech-to-pushforward spectral sequence

A composable pair of 1-morphisms of categories fibred in groupoids, with the
first covering by essential image, having equalizers on the source, and
faithful, yields a first-quadrant spectral sequence of abelian sheaves from
higher direct images along `g ∘ f_p` to the higher direct images of `g`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits FiberedCategoryOver.Groupoids
open scoped Bicategory Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {U X Y : GroupoidsOver S}

/-- The first-page object `R^q (g ∘ f_p)_* f_p⁻¹ F` of the relative Čech
pushforward spectral sequence, as an abelian sheaf on `𝒴_τ`. -/
noncomputable abbrev relativeCechPushforwardPageOne (f : U ⟶ X) (g : X ⟶ Y)
    (τ : StandardTopology) (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})
    (p q : ℕ)
    [HasSheafify (relativeCechSite f τ p) AddCommGrpCat.{u + 1}]
    [HasSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions (Sheaf (relativeCechSite f τ p) AddCommGrpCat.{u + 1})] :
    Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1} :=
  higherDirectImage (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌ ≫ g) τ
    (relativeCechInverseImage f τ F p) q

/-- Unfolding of `relativeCechPushforwardPageOne` as a higher direct image of
`f_p⁻¹ F` along `g ∘ f_p`. -/
theorem relativeCechPushforwardPageOne_obj (f : U ⟶ X) (g : X ⟶ Y)
    (τ : StandardTopology) (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})
    (p q : ℕ)
    [HasSheafify (relativeCechSite f τ p) AddCommGrpCat.{u + 1}]
    [HasSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions (Sheaf (relativeCechSite f τ p) AddCommGrpCat.{u + 1})] :
    relativeCechPushforwardPageOne f g τ F p q =
      higherDirectImage (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌ ≫ g) τ
        (relativeCechInverseImage f τ F p) q :=
  rfl

/-- A faithful morphism that locally covers by its essential image and whose source
has equalizers yields a first-quadrant spectral sequence of abelian sheaves. Its
first page consists of higher direct images of inverse images on covering
simplices, and it converges to the higher direct images of the coefficient sheaf. -/
theorem exists_relativeCechPushforwardSpectralSequence (f : U ⟶ X) (g : X ⟶ Y)
    (τ : StandardTopology) (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})
    (hf : coversByEssentialImage f τ)
    [HasEqualizers U.total] [Functor.Faithful (toFunctor f)]
    [HasSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}]
    [HasSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})]
    [∀ p : ℕ, HasSheafify (relativeCechSite f τ p) AddCommGrpCat.{u + 1}]
    [∀ p : ℕ, HasInjectiveResolutions
      (Sheaf (relativeCechSite f τ p) AddCommGrpCat.{u + 1})] :
    ∃ (E : CohomologicalSpectralSequenceNat
        (Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1}) 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅
          higherDirectImage (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌ ≫ g) τ
            (relativeCechInverseImage f τ F p) q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ higherDirectImage g τ F n) := sorry

end AlgebraicGeometry.GroupoidsOver
