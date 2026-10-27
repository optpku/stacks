/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.GlobalCohomology
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Cech.SpectralSequence
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.LowerShriek

/-!
# The relative Čech spectral sequence for module sheaves

Module cohomology on the covering simplices is a module over the global sections
of the target structure sheaf through the canonical projection pullback maps.
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

/-- The pullback of global sections of the structure sheaf along a covering-simplex
projection. -/
def relativeCechGlobalSectionsMap (f : U ⟶ X) (τ : StandardTopology) (p : ℕ) :
    SheafOfModules.GlobalCohomology.sectionsRing (associatedStructureSheaf X τ) →+*
      SheafOfModules.GlobalCohomology.sectionsRing
        (associatedStructureSheaf (Cech.covering.{u + 1, u, u + 1, u} f ⦋p⦌) τ) :=
  SheafOfModules.GlobalCohomology.sectionsPullback
    (associatedStructureSheaf (Cech.covering.{u + 1, u, u + 1, u} f ⦋p⦌) τ)
    (associatedStructureSheaf X τ) (toFunctor (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌))
    (associatedStructureSheafInverseImageIso (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌) τ).hom.hom

/-- Cohomology of the module inverse image on a covering simplex, with scalars
restricted to global sections of the target structure sheaf. -/
def relativeCechModulePageOneLinear (f : U ⟶ X) (τ : StandardTopology)
    (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (p q : ℕ)
    [HasSheafify (relativeCechSite f τ p) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (relativeCechSite f τ p) AddCommGrpCat.{u + 1})] :
    ModuleCat.{u + 1}
      (SheafOfModules.GlobalCohomology.sectionsRing (associatedStructureSheaf X τ)) :=
  (ModuleCat.restrictScalars (relativeCechGlobalSectionsMap f τ p)).obj
    (SheafOfModules.GlobalCohomology.obj
      (associatedStructureSheaf (Cech.covering.{u + 1, u, u + 1, u} f ⦋p⦌) τ)
      (relativeCechModuleInverseImage f τ F p) q)

/-- Forgetting the global-section scalar action recovers additive cohomology of
the module inverse image on the covering simplex. -/
theorem relativeCechModulePageOneLinear_forget (f : U ⟶ X) (τ : StandardTopology)
    (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (p q : ℕ)
    [HasSheafify (relativeCechSite f τ p) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (relativeCechSite f τ p) AddCommGrpCat.{u + 1})] :
    (forget₂ (ModuleCat.{u + 1}
        (SheafOfModules.GlobalCohomology.sectionsRing (associatedStructureSheaf X τ)))
      AddCommGrpCat.{u + 1}).obj (relativeCechModulePageOneLinear f τ F p q) =
      relativeCechModulePageOne f τ F p q := sorry

/-- A faithful morphism of categories fibred in groupoids whose source has equalizers
and whose essential image locally covers the target yields a first-quadrant spectral
sequence of modules over the global sections of the target structure sheaf. Its first
page is cohomology of module inverse images on covering simplices, and it converges
to cohomology of the coefficient module sheaf. -/
theorem exists_relativeCechModuleSpectralSequence (f : U ⟶ X) (τ : StandardTopology)
    (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ))
    (hf : coversByEssentialImage f τ)
    [HasEqualizers U.total] [Functor.Faithful (toFunctor f)]
    [HasSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})]
    [∀ p : ℕ, HasSheafify (relativeCechSite f τ p) AddCommGrpCat.{u + 1}]
    [∀ p : ℕ, HasExt.{u + 1} (Sheaf (relativeCechSite f τ p) AddCommGrpCat.{u + 1})] :
    ∃ (E : CohomologicalSpectralSequenceNat
        (ModuleCat.{u + 1}
          (SheafOfModules.GlobalCohomology.sectionsRing (associatedStructureSheaf X τ))) 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅ relativeCechModulePageOneLinear f τ F p q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ SheafOfModules.GlobalCohomology.obj (associatedStructureSheaf X τ) F n) := sorry

end AlgebraicGeometry.GroupoidsOver
