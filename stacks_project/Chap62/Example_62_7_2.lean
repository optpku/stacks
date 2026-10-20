module

public import ReasLib.AlgebraicGeometry.RelativeCycle.AffineLineOverPlane
import StacksCheckRecall

/-!
# Example 62.7.2

A relative 0-cycle on the affine line over the affine plane which is compatible
with specializations, but whose support closure contains the origin fibre and
so is not equidimensional.
-/

@[expose] public section

universe u

/- Example 62.7.2
Over any field, on the affine line over the affine plane, let `a` and `b` be
the residue-field images of `x` and `y` at each base point. The family is zero
when `b = 0` and otherwise is the difference of the rational-point cycles at
`a / b` and `(a + b²) / b`. It is compatible with specializations, its support
closure contains the whole fibre over `(0, 0)`, and it is not equidimensional.
-/
@[stacks 0H5J] #check (AlgebraicGeometry.AffineLineOverPlane.family_isRelative :
  ∀ (k : Type u) [Field k],
    AlgebraicGeometry.RelativeCycle.IsRelative
      (AlgebraicGeometry.AffineLineOverPlane.family k))

#check (AlgebraicGeometry.AffineLineOverPlane.closure_support_contains_originFiber :
  ∀ (k : Type u) [Field k],
    Set.range ((AlgebraicGeometry.AffineLineOverPlane.hom k).fiberι
      (AlgebraicGeometry.AffineLineOverPlane.origin k)) ⊆
      closure (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.support
        (AlgebraicGeometry.AffineLineOverPlane.family k)))

#check (AlgebraicGeometry.AffineLineOverPlane.not_equidimensional :
  ∀ (k : Type u) [Field k],
    ¬ AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.Equidimensional
      (AlgebraicGeometry.AffineLineOverPlane.family k))
