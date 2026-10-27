/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Pullback.EtaleRestriction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange.Pullback
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Pullback

/-! # Flat pullback and the quasi-coherent coreflector -/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
  [AlgebraicStack X] [AlgebraicStack Y]

/-- Quasi-coherent pullback commutes with inclusion into locally quasi-coherent
étale modules with flat base change via the topology-restriction comparison. -/
def QCoh.toLQCohFbc_pullback (f : X ⟶ Y) :
    QCoh.pullback f ⋙ QCoh.toLQCohFbc X ⟶
      QCoh.toLQCohFbc Y ⋙ LQCohFbc.inverseImage f where
  app G := homMk ((modulePullbackRestrictionIso f).hom.app G.obj)
  naturality := sorry

/-- The canonical comparison from pullback of the quasi-coherent coreflector
to the quasi-coherent coreflector of pullback is the mate of the inclusion square. -/
def LQCohFbc.toQCoh_pullback (f : X ⟶ Y) :
    LQCohFbc.toQCoh Y ⋙ QCoh.pullback f ⟶
      LQCohFbc.inverseImage f ⋙ LQCohFbc.toQCoh X :=
  (mateEquiv (QCoh.toLQCohFbcAdjunction Y) (QCoh.toLQCohFbcAdjunction X)
    (QCoh.toLQCohFbc_pullback f)).natTrans

/-- The coreflector comparison is the adjunct of the inclusion comparison
followed by inverse image of the canonical counit. -/
theorem LQCohFbc.toQCoh_pullback_app (f : X ⟶ Y) (F : LQCohFbc Y) :
    (LQCohFbc.toQCoh_pullback f).app F =
      (QCoh.toLQCohFbcAdjunction X).homEquiv _ _
        ((QCoh.toLQCohFbc_pullback f).app ((LQCohFbc.toQCoh Y).obj F) ≫
          (LQCohFbc.inverseImage f).map ((QCoh.toLQCohFbcAdjunction Y).counit.app F)) := sorry

/-- Flat pullback makes the canonical quasi-coherent coreflector comparison invertible. -/
instance LQCohFbc.toQCoh_pullback_isIso (f : X ⟶ Y) [AlgebraicStack.Flat f] :
    IsIso (LQCohFbc.toQCoh_pullback f) := sorry

/-- The quasi-coherent coreflector commutes canonically with flat pullback. -/
def LQCohFbc.toQCoh_pullbackIso (f : X ⟶ Y) [AlgebraicStack.Flat f] :
    LQCohFbc.inverseImage f ⋙ LQCohFbc.toQCoh X ≅
      LQCohFbc.toQCoh Y ⋙ QCoh.pullback f :=
  (asIso (LQCohFbc.toQCoh_pullback f)).symm

/-- The forward component of the flat-pullback isomorphism is the inverse
of the canonical coreflector comparison. -/
theorem LQCohFbc.toQCoh_pullback_hom_app (f : X ⟶ Y) [AlgebraicStack.Flat f]
    (F : LQCohFbc Y) :
    (LQCohFbc.toQCoh_pullbackIso f).hom.app F =
      inv ((LQCohFbc.toQCoh_pullback f).app F) := sorry

end AlgebraicGeometry.GroupoidsOver
