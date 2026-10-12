/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.RelativeDimension
import StacksCheckRecall

universe u

/- Definition 29.30.15: a morphism of schemes is syntomic of relative dimension `d` when it is
syntomic and the local dimension of its fibre at every source point is `d`. -/
@[stacks 02K2] #check
  (AlgebraicGeometry.SyntomicOfRelativeDimension :
    {X S : AlgebraicGeometry.Scheme.{u}} → (X ⟶ S) → ℕ → Prop)

#check
  (AlgebraicGeometry.syntomicOfRelativeDimension_iff :
    {X S : AlgebraicGeometry.Scheme.{u}} → (f : X ⟶ S) → (d : ℕ) →
      AlgebraicGeometry.SyntomicOfRelativeDimension f d ↔
        AlgebraicGeometry.Syntomic f ∧
          ∀ x : X, f.fiberDimensionAt x = (d : WithBot ℕ∞))
