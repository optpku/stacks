/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import ReasLib.RingTheory.Normal.Ring

/-!
# Normal schemes

This file defines normality of schemes through the normality of all local rings. It is the
scheme-level counterpart of `IsNormalRing` and exposes both pointwise and global forms for
downstream algebraic-geometry arguments.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- A scheme is normal at `x` when its stalk at `x` is a normal ring. -/
abbrev isNormalAt (x : X) : Prop :=
  _root_.IsNormalRing (X.presheaf.stalk x)

/-- `X.isNormalAt x` is equivalent to normality of the stalk at `x`. -/
@[simp]
theorem isNormalAt_iff (x : X) :
    X.isNormalAt x ↔ _root_.IsNormalRing (X.presheaf.stalk x) := sorry

/-- A normality-at-a-point hypothesis provides normality of the corresponding stalk. -/
theorem isNormalAt.isNormalRing {x : X} (hx : X.isNormalAt x) :
    _root_.IsNormalRing (X.presheaf.stalk x) := sorry

/-- A scheme normal at a point has a reduced stalk at that point. -/
theorem isNormalAt.isReduced {Y : Scheme.{u}} {y : Y} (hy : Y.isNormalAt y) :
    _root_.IsReduced (Y.presheaf.stalk y) := sorry

/-- A scheme is normal when it is normal at every point. -/
@[stacks 033I]
abbrev isNormal : Prop :=
  ∀ x : X, X.isNormalAt x

/-- `X.isNormal` is equivalent to normality at every point. -/
theorem isNormal_def :
    X.isNormal ↔ ∀ x : X, X.isNormalAt x := sorry

/-- A normal scheme is normal at each point. -/
theorem isNormal.isNormalAt (hX : X.isNormal) (x : X) :
    X.isNormalAt x := sorry

/-- A normal scheme has normal local rings. -/
theorem isNormal.isNormalRing_stalk (hX : X.isNormal) (x : X) :
    _root_.IsNormalRing (X.presheaf.stalk x) := sorry

/-- A scheme is normal if and only if each of its stalks is a normal ring. -/
@[simp]
theorem isNormal_iff :
    X.isNormal ↔ ∀ x : X, _root_.IsNormalRing (X.presheaf.stalk x) := sorry

/-- Every normal scheme is reduced. -/
theorem isReduced_of_isNormal {Y : Scheme.{u}} (hY : Y.isNormal) :
    AlgebraicGeometry.IsReduced Y := sorry

end AlgebraicGeometry.Scheme
