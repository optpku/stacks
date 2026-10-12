/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import stacks_project.Chap67.Lemma_67_8_10_Instances
public import stacks_project.Chap75.Lemma_75_6_1_Pushforward

/-!
# Right adjoint of derived pushforward on algebraic spaces

Restricted derived pushforward on `DerivedQCoh` along a morphism of
quasi-compact quasi-separated algebraic spaces is a left adjoint.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Derived pushforward on `DerivedQCoh` along a morphism of quasi-compact
quasi-separated algebraic spaces has a right adjoint. -/
instance pushforwardIsLeftAdjoint {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y] :
    (pushforward f).IsLeftAdjoint :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
