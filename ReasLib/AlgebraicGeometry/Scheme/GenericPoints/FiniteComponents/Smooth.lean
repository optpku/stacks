/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents.Locality
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smooth morphisms and finite irreducible components

This file records preservation of finiteness of irreducible components on quasi-compact opens
along smooth morphisms of schemes.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens

/-- A scheme smooth over a scheme whose quasi-compact opens have finitely many irreducible
components has the same finite-component property. -/
theorem of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y] :
    HasFiniteIrreducibleComponentsOnCompactOpens X := sorry

end AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens
