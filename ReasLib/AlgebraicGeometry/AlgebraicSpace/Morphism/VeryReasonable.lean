/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.VeryReasonable

/-!
# Very reasonable morphisms

A morphism is very reasonable when the source of every scheme base change is a very
reasonable algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism is very reasonable when every scheme-base-change apex is a very
reasonable algebraic space. -/
class VeryReasonable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- The apex of each scheme-base-change pullback square is very reasonable. -/
  ofOver_isPullback {T : Over S} {W : AlgebraicSpace S} {g : ofOver T ⟶ Y}
    {pT : W ⟶ ofOver T} {pX : W ⟶ X} :
    IsPullback pT pX g f → IsVeryReasonable W

namespace VeryReasonable

/-- Read the property from an actual scheme-base-change square. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} [VeryReasonable f]
    {T : Over S} {W : AlgebraicSpace S} {g : ofOver T ⟶ Y}
    {pT : W ⟶ ofOver T} {pX : W ⟶ X} (h : IsPullback pT pX g f) :
    IsVeryReasonable W :=
  VeryReasonable.ofOver_isPullback h

/-- The identity morphism is very reasonable. -/
instance id {S : Scheme.{u}} (X : AlgebraicSpace S) : VeryReasonable (𝟙 X) := sorry

end VeryReasonable

end AlgebraicGeometry.AlgebraicSpace
