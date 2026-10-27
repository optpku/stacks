/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Quasicoherent
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.InternalHom

/-! # Coreflection counits and topology restriction of modules -/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

namespace FppfModules.LQCohFbc

/-- The étale `LQCoh^{fbc}` module obtained by restricting an fppf
`LQCoh^{fbc}` module along `restriction`. -/
def restrict {X : GroupoidsOver S} [AlgebraicStack X]
    (F : FppfModules.LQCohFbc X) : GroupoidsOver.LQCohFbc X :=
  ⟨(restriction X).obj F.obj, F.property⟩

/-- The underlying étale module of `restrict F` is the restriction of `F`. -/
theorem restrict_obj {X : GroupoidsOver S} [AlgebraicStack X]
    (F : FppfModules.LQCohFbc X) :
    (GroupoidsOver.LQCohFbc.inclusion X).obj (restrict F) =
      (restriction X).obj F.obj :=
  rfl

end FppfModules.LQCohFbc

namespace LQCohFbc

/-- The adjunction counit `i(Q(F)) ⟶ F` of `toLQCohFbc ⊣ toQCoh`, viewed as a
morphism of étale modules. -/
def toQCohCounitApp {X : GroupoidsOver S} [AlgebraicStack X] (F : LQCohFbc X) :
    (inclusion X).obj ((QCoh.toLQCohFbc X).obj ((toQCoh X).obj F)) ⟶
      (inclusion X).obj F :=
  (inclusion X).map ((QCoh.toLQCohFbcAdjunction X).counit.app F)

end LQCohFbc

/-- The étale restriction of a quasi-coherent fppf module is quasi-coherent. -/
instance QCoh.restriction_obj_isQuasicoherent {X : GroupoidsOver S} (F : QCoh X) :
    ((restriction X).obj ((QCoh.inclusion X).obj F)).IsQuasicoherent :=
  sorry

namespace FppfModules.LQCohFbc

/-- The coreflection counit `Q(F) ⟶ F`, recovered as a morphism of fppf modules
from its étale restriction. -/
def toQCohCounitApp {X : GroupoidsOver S} [AlgebraicStack X]
    (F : FppfModules.LQCohFbc X) :
    (QCoh.inclusion X).obj
        ((GroupoidsOver.LQCohFbc.toQCoh X).obj (restrict F)) ⟶
      (FppfModules.inclusion X).obj F :=
  restrictionHomInv
    (GroupoidsOver.LQCohFbc.toQCohCounitApp (restrict F))

end FppfModules.LQCohFbc

end AlgebraicGeometry.GroupoidsOver
