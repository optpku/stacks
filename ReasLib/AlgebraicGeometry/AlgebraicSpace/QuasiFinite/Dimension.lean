/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.Locality

/-!
# A dimension criterion for quasi-finiteness of algebraic spaces

A zero-dimensional point in a field-valued fibre of a locally finite-type
morphism maps to a point where the morphism is quasi-finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- In a cartesian square of algebraic spaces over a scheme, with a locally
finite-type morphism and a field-valued point of its target, a zero-dimensional
point of the fibre maps to a point admitting an open neighbourhood on which
the original morphism is locally quasi-finite. -/
@[stacks 06LS]
theorem quasiFiniteAt_of_dimensionAt_eq_zero {S : Scheme.{u}}
    {X Y F : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : FieldValuedPoint Y) (p : F ⟶ X) (q : F ⟶ ofOver g.overObj)
    (hpb : IsPullback p q f g.hom) (z : Points F)
    (hz : dimensionAt z = (0 : WithBot ℕ∞)) :
    QuasiFiniteAt f (Points.map p z) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
