/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.UniverseLift
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CoefficientEquivalence
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRing

@[expose] public section
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u
namespace SheafOfModules.CoefficientPresentation

/-- Transport modules along a specified coefficient isomorphism on one fixed
site. Both functors are the explicit scalar-restriction functors. -/
def equivalence {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R T : Sheaf J RingCat.{u + 1}} (φ : R ≅ T) :
    SheafOfModules.{u + 1} R ≌ SheafOfModules.{u + 1} T := by
  let e := (CategoryTheory.Equivalence.refl : C ≌ C)
  -- Local instance justification (defeq pin): the specified site equivalence has exactly the identity base functor.
  letI : e.functor.IsContinuous J J := by
    change (𝟭 C).IsContinuous J J
    infer_instance
  -- Local instance justification (defeq pin): its inverse is the same identity functor on this one site.
  letI : e.inverse.IsContinuous J J := by
    change (𝟭 C).IsContinuous J J
    infer_instance
  exact (SheafOfModules.CoefficientEquivalence.equivalence (J:=J) (K:=J) e φ).symm

end SheafOfModules.CoefficientPresentation

namespace AlgebraicGeometry.GroupoidsOver.ModuleUniverseComparison
variable {S : Scheme.{u}}

/-- The two enlarged coefficient sheaves have identical lifted sections and
restriction maps. Both directions are the identity ring homomorphism. -/
def coefficientIso (X : GroupoidsOver S) :
    SheafOfModules.UniverseLift.ring (etaleStructureSheaf X) ≅
      (commEtaleRingedSiteLift X).structureSheaf :=
  (fullyFaithfulSheafToPresheaf X.etaleTopology RingCat.{u + 1}).preimageIso
    (NatIso.ofComponents (fun _ => Iso.refl _) (by intros; ext x; rfl))

/-- Changing between these two explicit coefficient presentations preserves
the module sections. This is an equivalence on the same BIG site. -/
def modules (X : GroupoidsOver S) :
    SheafOfModules.{u + 1} (SheafOfModules.UniverseLift.ring (etaleStructureSheaf X)) ≌
      RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X) :=
  SheafOfModules.CoefficientPresentation.equivalence (coefficientIso X)

/-- Original modules enter the existing canonical lifted ringed-site owner. -/
def lift (X : GroupoidsOver S) :
    etaleModules X ⥤ RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X) :=
  SheafOfModules.UniverseLift.functor (etaleStructureSheaf X) ⋙ (modules X).functor

/-- No shrinking or new carrier choice: the original sections are literally ULift. -/
theorem lift_carrier (X : GroupoidsOver S) (M : etaleModules X) (V : X.totalᵒᵖ) :
    (((lift X).obj M).val.obj V : Type (u + 1)) = ULift.{u + 1} (M.val.obj V) := rfl

end AlgebraicGeometry.GroupoidsOver.ModuleUniverseComparison

namespace AlgebraicGeometry.AlgebraicSpace.ModuleUniverseComparison
variable {S : Scheme.{u}}

/-- The ordinary explicit ring lift identifies with the existing commutative
small-étale ringed-site lift by identity maps on global sections. -/
def coefficientIso (X : AlgebraicSpace S) :
    SheafOfModules.UniverseLift.ring (structureSheaf X) ≅
      (commRingedSiteLift X).structureSheaf :=
  (fullyFaithfulSheafToPresheaf X.smallEtaleTopology RingCat.{u + 1}).preimageIso
    (NatIso.ofComponents (fun _ => Iso.refl _) (by intros; ext x; rfl))

/-- Coefficient presentation equivalence on the SAME small étale site. -/
def modules (X : AlgebraicSpace S) :
    SheafOfModules.{u + 1} (SheafOfModules.UniverseLift.ring (structureSheaf X)) ≌
      RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X) :=
  SheafOfModules.CoefficientPresentation.equivalence (coefficientIso X)

/-- Explicit lift of an original small-site module into its canonical larger owner. -/
def lift (X : AlgebraicSpace S) :
    X.Modules ⥤ RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X) :=
  SheafOfModules.UniverseLift.functor (structureSheaf X) ⋙ (modules X).functor

/-- The canonical-owner presentation retains exactly the original lifted sections. -/
theorem lift_carrier (X : AlgebraicSpace S) (M : X.Modules) (V : X.smallEtaleSiteᵒᵖ) :
    (((lift X).obj M).val.obj V : Type (u + 1)) = ULift.{u + 1} (M.val.obj V) := rfl

end AlgebraicGeometry.AlgebraicSpace.ModuleUniverseComparison
