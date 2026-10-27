/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.CohenMacaulay
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.OverField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Fiber.GeometricallyReduced
public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced

/-!
# Geometrically reduced families of curves

Geometric reducedness of the fibres is represented by an open of the base of
each family of curves. Over a field, this property agrees with geometric
reducedness of the corresponding proper scheme of dimension at most one.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object property of families of curves with geometrically reduced fibres. -/
def geometricallyReduced (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ ∀ y : Points (ofOver (base P)), y ∈ geometricallyReducedFiberLocus (hom P)

/-- Membership in `geometricallyReduced` means every fibre of the structure
morphism is geometrically reduced. -/
theorem geometricallyReduced_iff {S : Scheme.{u}} (P : Obj S) :
    geometricallyReduced S P ↔
      ∀ y : Points (ofOver (base P)), y ∈ geometricallyReducedFiberLocus (hom P) :=
  Iff.rfl

/-- Geometric reducedness of the fibres of a family of curves is invariant
under isomorphisms. -/
instance instIsClosedUnderIsomorphisms_geometricallyReduced (S : Scheme.{u}) :
    (geometricallyReduced S).IsClosedUnderIsomorphisms :=
  sorry

/-- For every family of curves, an open of its base represents geometric
reducedness of the fibres under every cartesian morphism of families. -/
theorem exists_geometricallyReduced_open {S : Scheme.{u}} (P : Obj S) :
    ∃ U : (base P).left.Opens, ∀ {Q : Obj S} (φ : Q ⟶ P),
      geometricallyReduced S Q ↔ Set.range (baseMap φ).left ⊆ U :=
  sorry

/-- A proper scheme of dimension at most one over a field defines a family
of curves with geometrically reduced fibres if and only if it is geometrically
reduced over the field. -/
theorem classifying_factorsThrough_geometricallyReduced_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    geometricallyReduced (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.geometricallyReduced X :=
  sorry

/-- Every family of curves with geometrically reduced fibres is Cohen–Macaulay. -/
theorem geometricallyReduced_le_cohenMacaulay (S : Scheme.{u}) :
    geometricallyReduced S ≤ cohenMacaulay S :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
