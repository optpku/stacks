module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic

/-!
# Syntomic morphisms of fixed relative dimension

This file records syntomic scheme morphisms whose fibres have a fixed local
dimension at every source point.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A scheme morphism is syntomic of relative dimension `d` when it is syntomic and the local
dimension of its fibre at every source point is `d`. -/
class SyntomicOfRelativeDimension {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) : Prop
    extends Syntomic f where
  /-- Every fibre has local dimension `d` at each source point. -/
  fiberDimensionAt_eq (x : X) : f.fiberDimensionAt x = (d : WithBot ℕ∞)

/-- A morphism is syntomic of relative dimension `d` exactly when it is syntomic and its local
fibre dimension at every source point equals `d`. -/
theorem syntomicOfRelativeDimension_iff {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) :
    SyntomicOfRelativeDimension f d ↔
      Syntomic f ∧ ∀ x : X, f.fiberDimensionAt x = (d : WithBot ℕ∞) := sorry

end AlgebraicGeometry
