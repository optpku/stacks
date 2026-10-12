/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap96.Lemma_96_17_6_LowerShriek
public import stacks_project.Chap96.Lemma_96_19_8

/-!
# The relative Čech-to-cohomology spectral sequence of modules

A 1-morphism of categories fibred in groupoids that covers by essential image,
has equalizers on the source, and is faithful, yields a first-quadrant spectral
sequence from cohomology of module inverse images on covering simplices to
global cohomology of a sheaf of modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits FiberedCategoryOver.Groupoids
open scoped Bicategory Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {U X : GroupoidsOver S}

/-- Inverse image `f_p^* F` of a sheaf of modules `F` on `𝒳_τ` along the covering-simplex
projection `f_p : 𝒰_p ⟶ 𝒳`. -/
noncomputable abbrev relativeCechModuleInverseImage (f : U ⟶ X) (τ : StandardTopology)
    (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (p : ℕ) :
    SheafOfModules.{u + 1}
      (associatedStructureSheaf (Cech.covering.{u + 1, u, u + 1, u} f ⦋p⦌) τ) :=
  (associatedModuleInverseImage (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌) τ).obj F

/-- Unfolding of `relativeCechModuleInverseImage` as module inverse image along `f_p`. -/
theorem relativeCechModuleInverseImage_obj (f : U ⟶ X) (τ : StandardTopology)
    (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (p : ℕ) :
    relativeCechModuleInverseImage f τ F p =
      (associatedModuleInverseImage (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌) τ).obj F :=
  rfl

/-- The first-page object `H^q((𝒰_p)_τ, f_p^* F)` of the relative Čech spectral sequence
of modules, computed on the underlying abelian sheaf. -/
noncomputable abbrev relativeCechModulePageOne (f : U ⟶ X) (τ : StandardTopology)
    (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (p q : ℕ)
    [HasSheafify (relativeCechSite f τ p) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (relativeCechSite f τ p) AddCommGrpCat.{u + 1})] :
    AddCommGrpCat.{u + 1} :=
  (Sheaf.functorH (relativeCechSite f τ p) q).obj
    ((SheafOfModules.toSheaf
        (associatedStructureSheaf (Cech.covering.{u + 1, u, u + 1, u} f ⦋p⦌) τ)).obj
      (relativeCechModuleInverseImage f τ F p))

/-- Unfolding of `relativeCechModulePageOne` as global cohomology of the underlying
abelian sheaf of `relativeCechModuleInverseImage`. -/
theorem relativeCechModulePageOne_obj (f : U ⟶ X) (τ : StandardTopology)
    (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (p q : ℕ)
    [HasSheafify (relativeCechSite f τ p) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (relativeCechSite f τ p) AddCommGrpCat.{u + 1})] :
    relativeCechModulePageOne f τ F p q =
      (Sheaf.functorH (relativeCechSite f τ p) q).obj
        ((SheafOfModules.toSheaf
            (associatedStructureSheaf (Cech.covering.{u + 1, u, u + 1, u} f ⦋p⦌) τ)).obj
          (relativeCechModuleInverseImage f τ F p)) :=
  rfl

/-- Lemma 96.19.9: Let `f : 𝒰 ⟶ 𝒳` be a 1-morphism of categories fibred in groupoids
over `(Sch/S)_fppf`. Let `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`. Assume `F` is
an object of `Mod(𝒳_τ, 𝒪_𝒳)`, every object of `𝒳` admits a covering `{xᵢ ⟶ x}` in
`𝒳_τ` such that each `xᵢ` is isomorphic to `f(uᵢ)` for some object of `𝒰`, the
category `𝒰` has equalizers, and the functor `f` is faithful. Then there is a
first-quadrant spectral sequence of `Γ(𝒪_𝒳)`-modules
`E₁^{p, q} = H^q((𝒰_p)_τ, f_p^* F) ⇒ H^{p+q}(𝒳_τ, F)` converging to the cohomology
of `F` in the `τ`-topology. The Lean owner is a first-quadrant spectral sequence in
`AddCommGrpCat` of the underlying abelian sheaf of the module pullback, matching
the project computation of module cohomology via `Sheaf.functorH` of `toSheaf`. -/
@[stacks 06XG]
theorem exists_relativeCechModuleSpectralSequence (f : U ⟶ X) (τ : StandardTopology)
    (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ))
    (hf : coversByEssentialImage f τ)
    [HasEqualizers U.total] [Functor.Faithful (toFunctor f)]
    [HasSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})]
    [∀ p : ℕ, HasSheafify (relativeCechSite f τ p) AddCommGrpCat.{u + 1}]
    [∀ p : ℕ, HasExt.{u + 1} (Sheaf (relativeCechSite f τ p) AddCommGrpCat.{u + 1})] :
    ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{u + 1} 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅ relativeCechModulePageOne f τ F p q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ (Sheaf.functorH (X.associatedTopology τ) n).obj
          ((SheafOfModules.toSheaf (associatedStructureSheaf X τ)).obj F)) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
