/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.PointwiseRegular
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.RingTheory.Normal.RegularLocal

/-!
# Regularity properties of smooth schemes over fields

This file relates geometric regularity over a field to pointwise smoothness and
records geometric regularity, normality, and reducedness consequences for
schemes smooth over fields.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- A locally finite type morphism to the spectrum of a field is smooth at a point exactly
when it is geometrically regular there. -/
@[stacks 038X]
theorem geometricallyRegularAt_iff_smoothAt
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] (x : X) :
    IsGeometricallyRegularAt f x ↔ f.SmoothAt x := sorry

/-- A scheme smooth over a field is regular. -/
theorem regular_of_smooth_over_field
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] : Scheme.Regular X := sorry

/-- A morphism to the spectrum of a field is geometrically regular when it is smooth. -/
@[stacks 056T]
theorem isGeometricallyRegular_of_smooth_over_field
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] : IsGeometricallyRegular f := sorry

/-- Smooth morphisms to spectra of fields are canonically geometrically regular. -/
instance instIsGeometricallyRegularOfSmoothOverField
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] : IsGeometricallyRegular f :=
  isGeometricallyRegular_of_smooth_over_field f

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- A scheme smooth over a field is geometrically normal over that field. -/
@[stacks 056T]
theorem geometricallyNormal_of_smooth
    (X : Over (Spec (CommRingCat.of k))) [Smooth X.hom] : geometricallyNormal X := sorry

/-- A scheme smooth over a field is geometrically reduced over that field. -/
@[stacks 056T]
theorem geometricallyReduced_of_smooth
    (X : Over (Spec (CommRingCat.of k))) [Smooth X.hom] : geometricallyReduced X := sorry

end AlgebraicGeometry.SchemeOverField

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- Every smooth morphism of schemes carries the canonical regularity instance. -/
instance instRegularOfSmooth (f : X ⟶ Y) [Smooth f] : Regular f := sorry

end AlgebraicGeometry
