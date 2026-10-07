module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension

/-!
# Quasi-finite morphisms and relative dimension zero

This leaf records the standard dimension-zero characterization of
quasi-finiteness at a point and along a morphism.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a locally finite-type morphism, quasi-finiteness at a point is
equivalent to zero local fibre dimension. -/
@[stacks 0397]
theorem quasiFiniteAt_iff_fiberDimensionAt_eq_zero {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) :
    f.QuasiFiniteAt x ↔ f.fiberDimensionAt x = (0 : WithBot ℕ∞) := sorry

/-- A locally finite-type morphism is locally quasi-finite exactly when it has
relative dimension zero. -/
@[stacks 0397]
theorem locallyQuasiFinite_iff_relativeDimension_zero {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] :
    LocallyQuasiFinite f ↔ RelativeDimension f 0 := sorry

end AlgebraicGeometry.Scheme.Hom
