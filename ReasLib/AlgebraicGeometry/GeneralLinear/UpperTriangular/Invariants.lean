/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GeneralLinear.UpperTriangular.Action

/-!
# Invariant functions for the upper-triangular action on `GL₂`

This file defines the invariant subring and identifies its elements with the scalar functions
over a field.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GLTwo.UpperTriangular

/-- Pullback on global functions along the source map. -/
def sourceComap (k : Type u) [CommRing k] :
    GLTwo.coordinateRing k →+* Γ((relation k).R.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (GLTwo.coordinateRing k))).inv ≫
    (relation k).s.left.appTop).hom

/-- `sourceComap` is the composite of the affine global-sections comparison and pullback along
the source map. -/
theorem sourceComap_eq (k : Type u) [CommRing k] :
    sourceComap k =
      ((Scheme.ΓSpecIso (CommRingCat.of (GLTwo.coordinateRing k))).inv ≫
        (relation k).s.left.appTop).hom := sorry

/-- Pullback on global functions along the target map. -/
def targetComap (k : Type u) [CommRing k] :
    GLTwo.coordinateRing k →+* Γ((relation k).R.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (GLTwo.coordinateRing k))).inv ≫
    (relation k).t.left.appTop).hom

/-- `targetComap` is the composite of the affine global-sections comparison and pullback along
the target map. -/
theorem targetComap_eq (k : Type u) [CommRing k] :
    targetComap k =
      ((Scheme.ΓSpecIso (CommRingCat.of (GLTwo.coordinateRing k))).inv ≫
        (relation k).t.left.appTop).hom := sorry

/-- The invariant subring of regular functions on `GL₂` for the upper-triangular action. -/
def invariantRing (k : Type u) [CommRing k] : Subring (GLTwo.coordinateRing k) :=
  (targetComap k).eqLocus (sourceComap k)

/-- Membership in the invariant ring is equality after pullback along target and source. -/
theorem mem_invariantRing (k : Type u) [CommRing k] (f : GLTwo.coordinateRing k) :
    f ∈ invariantRing k ↔ targetComap k f = sourceComap k f := sorry

/-- Over a field, the invariant regular functions are exactly the scalar functions. -/
theorem invariantRing_eq_scalars (k : Type u) [Field k] :
    invariantRing k = RingHom.range (algebraMap k (GLTwo.coordinateRing k)) := sorry

end AlgebraicGeometry.GLTwo.UpperTriangular
