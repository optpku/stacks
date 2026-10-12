/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap96.Lemma_96_19_12_Pushforward
public import stacks_project.Chap96.Lemma_96_19_9

/-!
# The relative Čech-to-pushforward spectral sequence of modules

A composable pair of 1-morphisms of categories fibred in groupoids, with the
first covering by essential image, having equalizers on the source, and
faithful, yields a first-quadrant spectral sequence of sheaves of modules from
higher direct images along `g ∘ f_p` to the higher direct images of `g`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits FiberedCategoryOver.Groupoids
open scoped Bicategory Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {U X Y : GroupoidsOver S}

/-- The first-page object `R^q (g ∘ f_p)_* f_p⁻¹ F` of the relative Čech module
pushforward spectral sequence, as a sheaf of modules on `𝒴_τ`. -/
noncomputable abbrev relativeCechModulePushforwardPageOne (f : U ⟶ X) (g : X ⟶ Y)
    (τ : StandardTopology) (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ))
    (p q : ℕ)
    [HasInjectiveResolutions
      (SheafOfModules.{u + 1}
        (associatedStructureSheaf (Cech.covering.{u + 1, u, u + 1, u} f ⦋p⦌) τ))] :
    SheafOfModules.{u + 1} (associatedStructureSheaf Y τ) :=
  associatedModuleHigherDirectImage (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌ ≫ g) τ
    (relativeCechModuleInverseImage f τ F p) q

/-- Unfolding of `relativeCechModulePushforwardPageOne` as a module-valued higher
direct image of `f_p⁻¹ F` along `g ∘ f_p`. -/
theorem relativeCechModulePushforwardPageOne_obj (f : U ⟶ X) (g : X ⟶ Y)
    (τ : StandardTopology) (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ))
    (p q : ℕ)
    [HasInjectiveResolutions
      (SheafOfModules.{u + 1}
        (associatedStructureSheaf (Cech.covering.{u + 1, u, u + 1, u} f ⦋p⦌) τ))] :
    relativeCechModulePushforwardPageOne f g τ F p q =
      associatedModuleHigherDirectImage (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌ ≫ g) τ
        (relativeCechModuleInverseImage f τ F p) q :=
  rfl

/-- Lemma 96.19.12: Let `f : 𝒰 ⟶ 𝒳` and `g : 𝒳 ⟶ 𝒴` be composable 1-morphisms of
categories fibred in groupoids over `(Sch/S)_fppf`. Let
`τ ∈ {Zariski, étale, smooth, syntomic, fppf}`. Assume `F` is an object of
`Mod(𝒳_τ, 𝒪_𝒳)`, every object of `𝒳` admits a covering `{xᵢ ⟶ x}` in `𝒳_τ`
such that each `xᵢ` is isomorphic to `f(uᵢ)` for some object of `𝒰`, the
category `𝒰` has equalizers, and the functor `f` is faithful. Then there is a
first-quadrant spectral sequence in `Mod(𝒴_τ, 𝒪_𝒴)`
`E₁^{p, q} = R^q (g ∘ f_p)_* f_p⁻¹ F ⇒ R^{p+q} g_* F`, where all higher direct
images are computed in the `τ`-topology. -/
@[stacks 072E]
theorem exists_relativeCechModulePushforwardSpectralSequence (f : U ⟶ X) (g : X ⟶ Y)
    (τ : StandardTopology) (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ))
    (hf : coversByEssentialImage f τ)
    [HasEqualizers U.total] [Functor.Faithful (toFunctor f)]
    [HasInjectiveResolutions (SheafOfModules.{u + 1} (associatedStructureSheaf X τ))]
    [∀ p : ℕ, HasInjectiveResolutions
      (SheafOfModules.{u + 1}
        (associatedStructureSheaf (Cech.covering.{u + 1, u, u + 1, u} f ⦋p⦌) τ))] :
    ∃ (E : CohomologicalSpectralSequenceNat
        (SheafOfModules.{u + 1} (associatedStructureSheaf Y τ)) 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅
          associatedModuleHigherDirectImage
            (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌ ≫ g) τ
            (relativeCechModuleInverseImage f τ F p) q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ associatedModuleHigherDirectImage g τ F n) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
