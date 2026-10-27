/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.UniverseLift
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CoefficientEquivalence
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.LocallyQuasiCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRing

@[expose] public section
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u
namespace SheafOfModules.CoefficientPresentation

/-- An isomorphism of coefficient sheaves on a fixed site induces an equivalence
of module categories by restriction of scalars in both directions. -/
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

namespace AlgebraicGeometry.GroupoidsOver

/-- Modules over the étale structure sheaf with coefficients enlarged to the
universe containing the objects of the site. -/
abbrev EtaleModulesLift {S : Scheme.{u}} (X : GroupoidsOver S) :=
  RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X)

end AlgebraicGeometry.GroupoidsOver

namespace AlgebraicGeometry.GroupoidsOver.ModuleUniverseComparison
variable {S : Scheme.{u}}

/-- The universe lift of the étale structure sheaf is isomorphic to the structure
sheaf of the lifted étale ringed site by identity maps on lifted sections. -/
def coefficientIso (X : GroupoidsOver S) :
    SheafOfModules.UniverseLift.ring (etaleStructureSheaf X) ≅
      (commEtaleRingedSiteLift X).structureSheaf :=
  (fullyFaithfulSheafToPresheaf X.etaleTopology RingCat.{u + 1}).preimageIso
    (NatIso.ofComponents (fun _ => Iso.refl _) (by intros; ext x; rfl))

/-- Transport along the coefficient isomorphism gives an equivalence of module
categories on the big étale site, preserving section carriers. -/
def modules (X : GroupoidsOver S) :
    SheafOfModules.{u + 1} (SheafOfModules.UniverseLift.ring (etaleStructureSheaf X)) ≌
      RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X) :=
  SheafOfModules.CoefficientPresentation.equivalence (coefficientIso X)

/-- Étale modules lift to modules over the enlarged structure sheaf by lifting
their coefficients and transporting along the coefficient isomorphism. -/
def lift (X : GroupoidsOver S) :
    etaleModules X ⥤ RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X) :=
  SheafOfModules.UniverseLift.functor (etaleStructureSheaf X) ⋙ (modules X).functor

/-- The section carrier of a lifted étale module is the universe lift of the
original section carrier. -/
theorem lift_carrier (X : GroupoidsOver S) (M : etaleModules X) (V : X.totalᵒᵖ) :
    (((lift X).obj M).val.obj V : Type (u + 1)) = ULift.{u + 1} (M.val.obj V) := rfl

end AlgebraicGeometry.GroupoidsOver.ModuleUniverseComparison

namespace AlgebraicGeometry.GroupoidsOver

/-- Local quasi-coherence is preserved and reflected by the explicit coefficient lift. -/
theorem isLocallyQuasiCoherent_lift_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    (F : etaleModules X) :
    IsLocallyQuasiCoherentLift ((ModuleUniverseComparison.lift X).obj F) ↔
      IsLocallyQuasiCoherent F :=
  sorry

end AlgebraicGeometry.GroupoidsOver

namespace AlgebraicGeometry.AlgebraicSpace.ModuleUniverseComparison
variable {S : Scheme.{u}}

/-- The universe lift of the structure sheaf is isomorphic to the structure sheaf
of the lifted small étale ringed site by identity maps on lifted sections. -/
def coefficientIso (X : AlgebraicSpace S) :
    SheafOfModules.UniverseLift.ring (structureSheaf X) ≅
      (commRingedSiteLift X).structureSheaf :=
  (fullyFaithfulSheafToPresheaf X.smallEtaleTopology RingCat.{u + 1}).preimageIso
    (NatIso.ofComponents (fun _ => Iso.refl _) (by intros; ext x; rfl))

/-- Transport along the coefficient isomorphism gives an equivalence of module
categories on the small étale site, preserving section carriers. -/
def modules (X : AlgebraicSpace S) :
    SheafOfModules.{u + 1} (SheafOfModules.UniverseLift.ring (structureSheaf X)) ≌
      RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X) :=
  SheafOfModules.CoefficientPresentation.equivalence (coefficientIso X)

/-- Modules on the small étale site lift to modules over the enlarged structure
sheaf by lifting coefficients and transporting along the coefficient isomorphism. -/
def lift (X : AlgebraicSpace S) :
    X.Modules ⥤ RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X) :=
  SheafOfModules.UniverseLift.functor (structureSheaf X) ⋙ (modules X).functor

/-- The section carrier of a lifted small étale module is the universe lift of
the original section carrier. -/
theorem lift_carrier (X : AlgebraicSpace S) (M : X.Modules) (V : X.smallEtaleSiteᵒᵖ) :
    (((lift X).obj M).val.obj V : Type (u + 1)) = ULift.{u + 1} (M.val.obj V) := rfl

end AlgebraicGeometry.AlgebraicSpace.ModuleUniverseComparison
