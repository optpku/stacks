/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Arrows in a module descent diagram

This file defines the three underlying additive maps obtained from a scalar-extension
isomorphism and compatible composites of ring homomorphisms.
-/

@[expose] public section

noncomputable section

universe u x

open CategoryTheory

namespace ModuleCat.DescentDiagram

variable {S S₂ S₃ : Type u}
variable [CommRing S] [CommRing S₂] [CommRing S₃]

/-- The source arrow from a module to the scalar extension along the target leg,
obtained from the unit along the source leg followed by the given comparison isomorphism. -/
def source (delta10 delta11 : S →+* S₂) (M : ModuleCat.{max u x} S)
    (theta : ModuleCat.ExtendScalars.obj' delta10 M ≅
      ModuleCat.ExtendScalars.obj' delta11 M) :
    AddCommGrpCat.of M ⟶
      AddCommGrpCat.of (ModuleCat.ExtendScalars.obj' delta11 M) :=
  (forget₂ (ModuleCat S) AddCommGrpCat).map
      ((ModuleCat.extendRestrictScalarsAdj delta10).unit.app M) ≫
    (forget₂ (ModuleCat S) AddCommGrpCat).map
      ((ModuleCat.restrictScalars delta10).map theta.hom)

/-- The upper arrow obtained by extending the comparison isomorphism and transporting
along the specified identifications of composite ring homomorphisms. -/
def upper (delta10 delta11 : S →+* S₂) (delta02 delta12 : S →+* S₃)
    (delta20 delta22 : S₂ →+* S₃) (M : ModuleCat.{max u x} S)
    (theta : ModuleCat.ExtendScalars.obj' delta10 M ≅
      ModuleCat.ExtendScalars.obj' delta11 M)
    (h20Target : delta02 = delta20.comp delta11)
    (h22Source : delta02 = delta22.comp delta10)
    (h22Target : delta12 = delta22.comp delta11) :
    AddCommGrpCat.of (ModuleCat.ExtendScalars.obj' delta11 M) ⟶
      AddCommGrpCat.of (ModuleCat.ExtendScalars.obj' delta12 M) :=
  let comparison20 :=
    (eqToIso (congrArg (fun phi ↦ ModuleCat.ExtendScalars.obj' phi M) h20Target)).trans
      ((ModuleCat.extendScalarsComp delta11 delta20).app M)
  let comparison22Source :=
    (eqToIso (congrArg (fun phi ↦ ModuleCat.ExtendScalars.obj' phi M) h22Source)).trans
      ((ModuleCat.extendScalarsComp delta10 delta22).app M)
  let comparison22Target :=
    (eqToIso (congrArg (fun phi ↦ ModuleCat.ExtendScalars.obj' phi M) h22Target)).trans
      ((ModuleCat.extendScalarsComp delta11 delta22).app M)
  let thetaTensorDelta22 := comparison22Source.hom ≫
    ModuleCat.ExtendScalars.map' delta22 theta.hom ≫ comparison22Target.inv
  (forget₂ (ModuleCat S₂) AddCommGrpCat).map
      ((ModuleCat.extendRestrictScalarsAdj delta20).unit.app
        (ModuleCat.ExtendScalars.obj' delta11 M)) ≫
    (forget₂ (ModuleCat S₃) AddCommGrpCat).map
      (comparison20.inv ≫ thetaTensorDelta22)

/-- The lower arrow obtained from the scalar-extension unit and transport along the
specified identification of the target composite ring homomorphism. -/
def lower (delta11 : S →+* S₂) (delta12 : S →+* S₃)
    (delta21 : S₂ →+* S₃) (M : ModuleCat.{max u x} S)
    (h21Target : delta12 = delta21.comp delta11) :
    AddCommGrpCat.of (ModuleCat.ExtendScalars.obj' delta11 M) ⟶
      AddCommGrpCat.of (ModuleCat.ExtendScalars.obj' delta12 M) :=
  let comparison21 :=
    (eqToIso (congrArg (fun phi ↦ ModuleCat.ExtendScalars.obj' phi M) h21Target)).trans
      ((ModuleCat.extendScalarsComp delta11 delta21).app M)
  (forget₂ (ModuleCat S₂) AddCommGrpCat).map
      ((ModuleCat.extendRestrictScalarsAdj delta21).unit.app
        (ModuleCat.ExtendScalars.obj' delta11 M)) ≫
    (forget₂ (ModuleCat S₃) AddCommGrpCat).map comparison21.inv

end ModuleCat.DescentDiagram
