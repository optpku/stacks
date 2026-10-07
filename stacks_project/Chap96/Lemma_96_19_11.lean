module

public import stacks_project.Chap96.Lemma_96_19_8
public import stacks_project.Chap96.Lemma_96_21_2_HigherDirectImage

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

/-- Lemma 96.19.11: Let `f : 𝒰 ⟶ 𝒳` and `g : 𝒳 ⟶ 𝒴` be composable 1-morphisms of
categories fibred in groupoids over `(Sch/S)_fppf`. Let
`τ ∈ {Zariski, étale, smooth, syntomic, fppf}`. Assume `F` is an abelian sheaf on
`𝒳_τ`, every object of `𝒳` admits a covering `{xᵢ ⟶ x}` in `𝒳_τ` such that each
`xᵢ` is isomorphic to `f(uᵢ)` for some object of `𝒰`, the category `𝒰` has
equalizers, and the functor `f` is faithful. Then there is a first-quadrant
spectral sequence of abelian sheaves on `𝒴_τ`
`E₁^{p, q} = R^q (g ∘ f_p)_* f_p⁻¹ F ⇒ R^{p+q} g_* F`, where all higher direct
images are computed in the `τ`-topology. -/
@[stacks 072D]
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
        (fun n ↦ higherDirectImage g τ F n) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
