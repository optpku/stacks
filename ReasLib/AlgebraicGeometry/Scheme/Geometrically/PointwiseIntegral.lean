module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic

/-!
# Geometrically pointwise integral schemes

This leaf records the stalkwise field-extension formulation of geometric
pointwise integrality for schemes over a field.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- A scheme over a field is geometrically pointwise integral at a point when every point
above it after every field-extension base change has an integral-domain stalk. -/
@[stacks 020H]
class IsGeometricallyPointwiseIntegralAt (f : X ⟶ Spec (CommRingCat.of k)) (x : X) : Prop where
  /-- Every field-extension base-change point above `x` has an integral-domain stalk. -/
  isDomain_stalk :
    ∀ (K : Type u) [Field K] [Algebra k K],
      ∀ x' : FieldExtension.baseChange k K f,
        FieldExtension.toSource k K f x' = x →
          IsDomain ((FieldExtension.baseChange k K f).presheaf.stalk x')

/-- Unfold geometric pointwise integrality at a point into its stalkwise field-extension
condition. -/
theorem isGeometricallyPointwiseIntegralAt_iff (x : X) :
    IsGeometricallyPointwiseIntegralAt f x ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        ∀ x' : FieldExtension.baseChange k K f,
          FieldExtension.toSource k K f x' = x →
            IsDomain ((FieldExtension.baseChange k K f).presheaf.stalk x') := sorry

/-- A scheme over a field is geometrically pointwise integral when it is geometrically
pointwise integral at every point. -/
@[stacks 020H]
class IsGeometricallyPointwiseIntegral (f : X ⟶ Spec (CommRingCat.of k)) : Prop where
  /-- Geometric pointwise integrality holds at every point of the source scheme. -/
  isGeometricallyPointwiseIntegralAt : ∀ x : X, IsGeometricallyPointwiseIntegralAt f x

/-- A geometrically integral scheme over `k` is geometrically pointwise integral. -/
@[stacks 020H, instance]
instance instIsGeometricallyPointwiseIntegralOfGeometricallyIntegral
    [GeometricallyIntegral f] : IsGeometricallyPointwiseIntegral f := sorry

/-- A geometrically pointwise integral scheme is geometrically pointwise integral at each point. -/
@[stacks 020H, instance]
instance instIsGeometricallyPointwiseIntegralAt (x : X)
    [h : IsGeometricallyPointwiseIntegral f] :
    IsGeometricallyPointwiseIntegralAt f x :=
  h.isGeometricallyPointwiseIntegralAt x

/-- Unfold geometric pointwise integrality into the pointwise condition. -/
theorem isGeometricallyPointwiseIntegral_iff :
    IsGeometricallyPointwiseIntegral f ↔
      ∀ x : X, IsGeometricallyPointwiseIntegralAt f x := sorry

/-- A scheme over a field is geometrically integral exactly when every field-extension base
change is integral. -/
@[stacks 020H]
theorem geometricallyIntegral_iff_forall_isIntegral_pullback :
    GeometricallyIntegral f ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        IsIntegral (FieldExtension.baseChange k K f) := sorry

end AlgebraicGeometry.Scheme.Hom
