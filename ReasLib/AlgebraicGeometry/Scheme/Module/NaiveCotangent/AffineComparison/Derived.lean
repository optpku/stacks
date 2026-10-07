module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.AffineComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape HomologicalComplex
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.NaiveCotangent

/-- The affine comparison for the naive cotangent complex is an isomorphism after passing to
the derived category. -/
@[stacks 0D0I]
theorem affineComparison_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) [hV : Fact (IsAffineOpen V)] (e : U ≤ f ⁻¹ᵁ V) :
    IsIso (DerivedCategory.Q.map (affineComparison f hU e)) := sorry

end AlgebraicGeometry.Scheme.Hom.NaiveCotangent
