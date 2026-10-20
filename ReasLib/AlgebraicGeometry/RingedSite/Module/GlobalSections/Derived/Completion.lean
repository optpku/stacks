/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived
public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Completion.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.OverSections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExtendedCech
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Derived completion and sections over an object of a ringed site

For a finite-type ideal sheaf generated over an object by a finite family, derived sections
of a completion are the derived completion of sections at the ideal spanned by that family.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open Opposite
open RingedSite.Hom
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.ExtendedCech

noncomputable section

universe u

namespace RingedSite.Hom.ModuleDerived

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}

/-- Derived sections of an ideal-sheaf completion target are complete with respect to the
ideal in `O(U)` spanned by the chosen generators. -/
private theorem derivedSectionsCompletionTarget_isComplete
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (U : C) {r : ℕ}
    (f : Fin r → (unitModule (J.over U) (O.over U)).sections)
    (hgen : generatedIdeal f = imageSubobject (I.arrow.over U))
    {K Khat : RingedSiteDerived J O} (eta : K ⟶ Khat)
    (heta : IsDerivedCompletion.{u, u, u, u} I eta) :
    DerivedCategory.IsDerivedCompleteWithRespectTo (A := O.obj.obj (op U))
      ((moduleSectionsDerived (RingedSite.ofCommRingSheaf J O) U).obj Khat)
      (Ideal.span (α := O.obj.obj (op U))
        (Set.range (fun i ↦ SheafOfModules.sectionsOverEquiv (unitModule J O) U (f i)))) := sorry

/-- The canonical comparison from the derived completion of `RΓ(U, K)` at the ideal spanned
by the chosen generators to `RΓ(U, Khat)`. -/
@[no_expose]
noncomputable def derivedSectionsCompletionComparison
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (U : C) {r : ℕ}
    (f : Fin r → (unitModule (J.over U) (O.over U)).sections)
    (hgen : generatedIdeal f = imageSubobject (I.arrow.over U))
    {K Khat : RingedSiteDerived J O} (eta : K ⟶ Khat)
    (heta : IsDerivedCompletion.{u, u, u, u} I eta) :
    derivedCompletionOf (A := O.obj.obj (op U))
      (Ideal.span (α := O.obj.obj (op U))
        (Set.range (fun i ↦ SheafOfModules.sectionsOverEquiv (unitModule J O) U (f i))))
        (Submodule.fg_span (Set.finite_range _))
      ((moduleSectionsDerived (RingedSite.ofCommRingSheaf J O) U).obj K) ⟶
      (moduleSectionsDerived (RingedSite.ofCommRingSheaf J O) U).obj Khat :=
  DerivedCompletion.lift (A := O.obj.obj (op U))
    (Ideal.span (α := O.obj.obj (op U))
        (Set.range (fun i ↦ SheafOfModules.sectionsOverEquiv (unitModule J O) U (f i))))
      (Submodule.fg_span (Set.finite_range _))
    (derivedSectionsCompletionTarget_isComplete I U f hgen eta heta)
      ((moduleSectionsDerived (RingedSite.ofCommRingSheaf J O) U).map eta)

/-- The completion unit followed by the comparison is the morphism on derived sections induced
by the ideal-sheaf completion map. -/
private theorem toDerivedCompletion_comp_derivedSectionsCompletionComparison
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (U : C) {r : ℕ}
    (f : Fin r → (unitModule (J.over U) (O.over U)).sections)
    (hgen : generatedIdeal f = imageSubobject (I.arrow.over U))
    {K Khat : RingedSiteDerived J O} (eta : K ⟶ Khat)
    (heta : IsDerivedCompletion.{u, u, u, u} I eta) :
    toDerivedCompletion (A := O.obj.obj (op U))
      (Ideal.span (α := O.obj.obj (op U))
        (Set.range (fun i ↦ SheafOfModules.sectionsOverEquiv (unitModule J O) U (f i))))
        (Submodule.fg_span (Set.finite_range _))
      ((moduleSectionsDerived (RingedSite.ofCommRingSheaf J O) U).obj K) ≫
      derivedSectionsCompletionComparison I U f hgen eta heta =
        (moduleSectionsDerived (RingedSite.ofCommRingSheaf J O) U).map eta := by
  exact DerivedCompletion.toDerivedCompletion_comp_lift _ _
    (derivedSectionsCompletionTarget_isComplete I U f hgen eta heta)
    ((moduleSectionsDerived (RingedSite.ofCommRingSheaf J O) U).map eta)

/-- The canonical comparison from the derived completion of `RΓ(U, K)` with
respect to the ideal spanned by the chosen generators to `RΓ(U, Khat)` is an isomorphism. -/
@[stacks 0CQI]
theorem derivedSectionsCompletionComparisonIsIso
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (U : C) {r : ℕ}
    (f : Fin r → (unitModule (J.over U) (O.over U)).sections)
    (hgen : generatedIdeal f = imageSubobject (I.arrow.over U))
    {K Khat : RingedSiteDerived J O} (eta : K ⟶ Khat)
    (heta : IsDerivedCompletion.{u, u, u, u} I eta) :
    IsIso (derivedSectionsCompletionComparison I U f hgen eta heta) := sorry

end RingedSite.Hom.ModuleDerived
