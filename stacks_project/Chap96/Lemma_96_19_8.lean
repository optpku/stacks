/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Abutment
public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology
public import stacks_project.Chap96.Lemma_96_18_1_CoveringSimplex
public import stacks_project.Chap96.Lemma_96_19_6_Covering

/-!
# The relative Čech-to-cohomology spectral sequence

A 1-morphism of categories fibred in groupoids that covers by essential image,
has equalizers on the source, and is faithful, yields a first-quadrant spectral
sequence from cohomology on covering simplices to global cohomology.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits FiberedCategoryOver.Groupoids
open scoped Bicategory Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {U X : GroupoidsOver S}

/-- The associated `τ`-site `(𝒰_p)_τ` of the covering simplex of `f`. -/
noncomputable abbrev relativeCechSite (f : U ⟶ X) (τ : StandardTopology) (p : ℕ) :
    GrothendieckTopology (Cech.covering.{u + 1, u, u + 1, u} f ⦋p⦌).total :=
  associatedTopology (Cech.covering.{u + 1, u, u + 1, u} f ⦋p⦌) τ

/-- Unfolding of `relativeCechSite` as the associated `τ`-topology of `𝒰_p`. -/
theorem relativeCechSite_eq (f : U ⟶ X) (τ : StandardTopology) (p : ℕ) :
    relativeCechSite f τ p =
      associatedTopology (Cech.covering.{u + 1, u, u + 1, u} f ⦋p⦌) τ :=
  rfl

/-- Inverse image `f_p⁻¹ F` of an abelian sheaf `F` on `𝒳_τ` along the covering-simplex
projection `f_p : 𝒰_p ⟶ 𝒳`. -/
noncomputable abbrev relativeCechInverseImage (f : U ⟶ X) (τ : StandardTopology)
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (p : ℕ) :
    Sheaf (relativeCechSite f τ p) AddCommGrpCat.{u + 1} :=
  ((toCartesianBasedFunctor (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌)).toFunctor.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (relativeCechSite f τ p) (X.associatedTopology τ)).obj F

/-- Unfolding of `relativeCechInverseImage` as continuous sheaf pushforward along `f_p`. -/
theorem relativeCechInverseImage_obj (f : U ⟶ X) (τ : StandardTopology)
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (p : ℕ) :
    relativeCechInverseImage f τ F p =
      ((toCartesianBasedFunctor (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌)).toFunctor.sheafPushforwardContinuous
          AddCommGrpCat.{u + 1} (relativeCechSite f τ p) (X.associatedTopology τ)).obj F :=
  rfl

/-- The first-page object `H^q((𝒰_p)_τ, f_p⁻¹ F)` of the relative Čech spectral sequence. -/
noncomputable abbrev relativeCechPageOne (f : U ⟶ X) (τ : StandardTopology)
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (p q : ℕ)
    [HasSheafify (relativeCechSite f τ p) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (relativeCechSite f τ p) AddCommGrpCat.{u + 1})] :
    AddCommGrpCat.{u + 1} :=
  (Sheaf.functorH (relativeCechSite f τ p) q).obj (relativeCechInverseImage f τ F p)

/-- Unfolding of `relativeCechPageOne` as global cohomology of `relativeCechInverseImage`. -/
theorem relativeCechPageOne_obj (f : U ⟶ X) (τ : StandardTopology)
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (p q : ℕ)
    [HasSheafify (relativeCechSite f τ p) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (relativeCechSite f τ p) AddCommGrpCat.{u + 1})] :
    relativeCechPageOne f τ F p q =
      (Sheaf.functorH (relativeCechSite f τ p) q).obj (relativeCechInverseImage f τ F p) :=
  rfl

/-- Lemma 96.19.8: Let `f : 𝒰 ⟶ 𝒳` be a 1-morphism of categories fibred in groupoids
over `(Sch/S)_fppf`. Let `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`. Assume `F` is
an abelian sheaf on `𝒳_τ`, every object of `𝒳` admits a covering `{xᵢ ⟶ x}` in `𝒳_τ`
such that each `xᵢ` is isomorphic to `f(uᵢ)` for some object of `𝒰`, the category `𝒰`
has equalizers, and the functor `f` is faithful. Then there is a first-quadrant spectral
sequence of abelian groups `E₁^{p, q} = H^q((𝒰_p)_τ, f_p⁻¹ F) ⇒ H^{p+q}(𝒳_τ, F)`
converging to the cohomology of `F` in the `τ`-topology. -/
@[stacks 06XF]
theorem exists_relativeCechSpectralSequence (f : U ⟶ X) (τ : StandardTopology)
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})
    (hf : coversByEssentialImage f τ)
    [HasEqualizers U.total] [Functor.Faithful (toFunctor f)]
    [HasSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})]
    [∀ p : ℕ, HasSheafify (relativeCechSite f τ p) AddCommGrpCat.{u + 1}]
    [∀ p : ℕ, HasExt.{u + 1} (Sheaf (relativeCechSite f τ p) AddCommGrpCat.{u + 1})] :
    ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{u + 1} 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅ relativeCechPageOne f τ F p q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ (Sheaf.functorH (X.associatedTopology τ) n).obj F) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
