module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Fiber
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- 33.16.3.1: for a scheme morphism `f : X ⟶ Y` and a point `x : X`, the relative tangent
space at `x` is canonically `κ(x)`-linearly equivalent to the tangent space of the
scheme-theoretic fiber over `f x` at `f.asFiber x`. -/
@[stacks 0BEA] #check
  (AlgebraicGeometry.Scheme.Hom.relativeTangentSpaceAt_eq_fiberRelativeTangentSpaceAt :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X),
      Scheme.Hom.relativeTangentSpaceAt f x ≃ₗ[X.residueField x]
        Scheme.Hom.fiberRelativeTangentSpaceAt f x)
