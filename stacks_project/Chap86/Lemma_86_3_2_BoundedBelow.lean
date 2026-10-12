/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import stacks_project.Chap67.Lemma_67_8_10_Instances
public import stacks_project.Chap75.Lemma_75_6_1_Pushforward

/-!
# Lower bound for the right adjoint of derived pushforward

A chosen right adjoint of restricted derived pushforward on `DerivedQCoh`
along a morphism of quasi-compact quasi-separated algebraic spaces preserves
lower cohomological bounds up to a uniform integer shift.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- A right adjoint to derived quasicoherent pushforward along a morphism of
quasi-compact quasi-separated algebraic spaces preserves lower cohomological bounds
up to a uniform integer shift. -/
theorem rightAdjoint_uniformLowerBound {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (f : X ⟶ Y) (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (adj : pushforward f ⊣ a) :
    ∃ N : ℤ, ∀ (K : DerivedQCoh Y) (c : ℤ),
      K.obj.IsGE (c + 1) → (a.obj K).obj.IsGE (c - N + 1) :=
  sorry

/-- A right adjoint to derived quasicoherent pushforward along a morphism of
quasi-compact quasi-separated algebraic spaces sends bounded-below objects to
bounded-below objects. -/
theorem rightAdjoint_mapsBoundedBelow {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (f : X ⟶ Y) (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (adj : pushforward f ⊣ a) (K : DerivedQCoh Y)
    (hK : K.obj.IsBoundedBelow) : (a.obj K).obj.IsBoundedBelow :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
