/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Cech.ModuleSpectralSequence
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits FiberedCategoryOver.Groupoids
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory Simplicial

universe u

variable {S : Scheme.{u}} {U X : GroupoidsOver S}

/- Lemma 96.19.9. The relative Čech-to-cohomology spectral sequence of
Γ(𝒪_𝒳)-modules for a faithful morphism with source equalizers and locally covering
essential image. -/
@[stacks 06XG] #check
  (AlgebraicGeometry.GroupoidsOver.exists_relativeCechModuleSpectralSequence :
    ∀ (f : U ⟶ X) (τ : StandardTopology)
      (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ))
      (_ : coversByEssentialImage f τ)
      [HasEqualizers U.total] [Functor.Faithful (toFunctor f)]
      [HasSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}]
      [HasExt.{u + 1} (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})]
      [∀ p : ℕ, HasSheafify (relativeCechSite f τ p) AddCommGrpCat.{u + 1}]
      [∀ p : ℕ, HasExt.{u + 1} (Sheaf (relativeCechSite f τ p) AddCommGrpCat.{u + 1})],
    ∃ (E : CohomologicalSpectralSequenceNat
        (ModuleCat.{u + 1}
          (SheafOfModules.GlobalCohomology.sectionsRing (associatedStructureSheaf X τ))) 1)
      (_ : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅ relativeCechModulePageOneLinear f τ F p q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ SheafOfModules.GlobalCohomology.obj (associatedStructureSheaf X τ) F n))
