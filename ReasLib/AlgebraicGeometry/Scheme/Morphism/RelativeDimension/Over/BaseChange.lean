/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Operations

/-!
# Relative dimension in slices under base change

This file records preservation of fixed relative dimension by the canonical
pullback functor between slice categories of schemes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.RelativeDimension

/-- A morphism of fixed relative dimension in a slice has the same relative dimension after
applying the canonical pullback functor. -/
instance instOverPullbackMap {S S' : Scheme.{u}} (g : S' ⟶ S)
    {X Y : Over S} (f : X ⟶ Y) (r : ℕ) [RelativeDimension f.left r] :
    RelativeDimension ((Over.pullback g).map f).left r :=
  MorphismProperty.overPullbackMap
    (P := fun (_ _ : Scheme.{u}) h ↦ RelativeDimension h r) g f inferInstance

end AlgebraicGeometry.Scheme.Hom.RelativeDimension
