/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic
import StacksCheckRecall

@[expose] public section

universe u

/-!
# Definition 29.30.1

This chapter entry is a compatibility facade for the scheme-level syntomic
morphism API.
-/

/- Definition 29.30.1: syntomicity at a point of the source scheme. -/
@[stacks 01UC] #check
  (AlgebraicGeometry.SyntomicAt :
    {X S : AlgebraicGeometry.Scheme.{u}} → (X ⟶ S) → X → Prop)

#check
  (AlgebraicGeometry.Syntomic :
    {X S : AlgebraicGeometry.Scheme.{u}} → (X ⟶ S) → Prop)

#check
  (AlgebraicGeometry.IsLocalCompleteIntersectionOver :
    (k : Type u) → [Field k] → {X : AlgebraicGeometry.Scheme.{u}} →
      (X ⟶ AlgebraicGeometry.Scheme.Spec.obj
        (Opposite.op (CommRingCat.of k))) → Prop)
