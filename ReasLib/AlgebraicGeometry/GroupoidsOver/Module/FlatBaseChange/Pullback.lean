/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.FlatBaseChange.Properties
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.LocallyQuasiCoherent.Pullback

/-! # Pullback of locally quasi-coherent modules with flat base change -/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.LQCohFbc

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
  [AlgebraicStack X] [AlgebraicStack Y]

/-- Étale inverse image preserves local quasi-coherence and flat base change. -/
theorem inverseImage_mapsTo (f : X ⟶ Y) (F : LQCohFbc Y) :
    lqcohFbc X ((etaleModuleInverseImage f).obj F.obj) := sorry

/-- Inverse image on locally quasi-coherent étale modules with flat base change
is the restriction of the ambient étale module inverse image. -/
def inverseImage (f : X ⟶ Y) : LQCohFbc Y ⥤ LQCohFbc X :=
  (lqcohFbc X).lift (inclusion Y ⋙ etaleModuleInverseImage f) (inverseImage_mapsTo f)

/-- Forgetting the restricted inverse image recovers étale module inverse image. -/
theorem inverseImage_comp_inclusion (f : X ⟶ Y) :
    inverseImage f ⋙ inclusion X = inclusion Y ⋙ etaleModuleInverseImage f := sorry

end AlgebraicGeometry.GroupoidsOver.LQCohFbc
