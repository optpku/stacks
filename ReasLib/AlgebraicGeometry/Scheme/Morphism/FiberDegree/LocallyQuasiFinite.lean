module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree

/-!
# Fibre degrees of locally quasi-finite morphisms

This file records uniform boundedness of fibre degrees for locally finite-type,
locally quasi-finite morphisms with quasi-compact source.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace LocallyQuasiFinite

/-- A locally finite-type, locally quasi-finite morphism with quasi-compact source has
universally bounded fibres. -/
theorem universallyBoundedFibres
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [CompactSpace X] :
    Scheme.Hom.universallyBoundedFibres f := sorry

end LocallyQuasiFinite
end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

/-- A locally finite-type, locally quasi-finite morphism with compact source has finite point
fibres. -/
instance tendstoCofinite_of_compactSource {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [CompactSpace X] :
    Filter.TendstoCofinite (fun x : X ↦ f x) := sorry

end AlgebraicGeometry.Scheme.Hom
