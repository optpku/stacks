/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local

/-!
# Groupoid arrow schemes over a field

This module equips the arrow scheme of a groupoid scheme with the field structures induced by
its source and target maps.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidScheme

section FieldBase

variable {S : Scheme.{u}} (G : GroupoidScheme S) {k : Type u} [Field k]
variable (uIso : G.U.left ≅ Spec (CommRingCat.of k))

/-- The arrow scheme of `G`, viewed as a scheme over `k` through the source map. -/
noncomputable abbrev arrowSourceOverField : SchemeOverField k :=
  Over.mk (G.s.left ≫ uIso.hom)

/-- The arrow scheme of `G`, viewed as a scheme over `k` through the target map. -/
noncomputable abbrev arrowTargetOverField : SchemeOverField k :=
  Over.mk (G.t.left ≫ uIso.hom)

/-- The underlying scheme of the source-induced field presentation is the arrow scheme. -/
@[simp]
theorem arrowSourceOverField_left :
    (arrowSourceOverField G uIso).left = G.R.left := rfl

/-- The structure morphism of the source-induced field presentation is the source map followed
by the chosen identification of the object scheme with `Spec k`. -/
@[simp]
theorem arrowSourceOverField_hom :
    (arrowSourceOverField G uIso).hom = G.s.left ≫ uIso.hom := rfl

/-- The underlying scheme of the target-induced field presentation is the arrow scheme. -/
@[simp]
theorem arrowTargetOverField_left :
    (arrowTargetOverField G uIso).left = G.R.left := rfl

/-- The structure morphism of the target-induced field presentation is the target map followed
by the chosen identification of the object scheme with `Spec k`. -/
@[simp]
theorem arrowTargetOverField_hom :
    (arrowTargetOverField G uIso).hom = G.t.left ≫ uIso.hom := rfl

/-- Local finite type of the source map makes the source-induced field presentation locally
algebraic. -/
theorem locallyAlgebraicArrowSourceOverField [LocallyOfFiniteType G.s.left] :
    LocallyAlgebraic (arrowSourceOverField G uIso) := by
  change LocallyOfFiniteType (G.s.left ≫ uIso.hom)
  infer_instance

/-- Local finite type of the target map makes the target-induced field presentation locally
algebraic. -/
theorem locallyAlgebraicArrowTargetOverField [LocallyOfFiniteType G.t.left] :
    LocallyAlgebraic (arrowTargetOverField G uIso) := by
  change LocallyOfFiniteType (G.t.left ≫ uIso.hom)
  infer_instance

end FieldBase

end AlgebraicGeometry.GroupoidScheme
