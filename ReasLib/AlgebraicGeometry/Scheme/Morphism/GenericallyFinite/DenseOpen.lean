/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.GenericallyFinite

/-!
# Generically finite morphisms over dense opens

This file relates finiteness of the fibers over the generic points of the target to finiteness
after restriction to a dense open subscheme of the target.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A locally finite type morphism that is generically finite on the target is finite over a
dense open of the target, provided the target has finitely many generic points and the morphism
is quasi-compact. -/
theorem GenericallyFiniteOnTarget.exists_dense_open_isFinite_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hf : f.GenericallyFiniteOnTarget)
    (hY : (genericPoints Y).Finite)
    (hqc : QuasiCompact f) :
    ∃ V : Y.Opens, Dense (V : Set Y) ∧ IsFinite (f ∣_ V) := sorry

/-- A locally finite type morphism is finite over a dense open of the target when the source and
target have finitely many generic points, the inverse image of the target generic points is
exactly the source generic points, and the morphism is either quasi-compact or separated. -/
theorem exists_dense_open_isFinite_restrict_of_preimage_genericPoints_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hX : (genericPoints X).Finite)
    (hY : (genericPoints Y).Finite)
    (hpreimage : f.base ⁻¹' genericPoints Y = genericPoints X)
    (hqc_or_sep : QuasiCompact f ∨ IsSeparated f) :
    ∃ V : Y.Opens, Dense (V : Set Y) ∧ IsFinite (f ∣_ V) := sorry

end AlgebraicGeometry.Scheme.Hom
