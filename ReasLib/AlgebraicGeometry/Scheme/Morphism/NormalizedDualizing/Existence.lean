/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Gluing.TwoOpen
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing.Uniqueness

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
namespace NormalizedDualizingComplexOnCover

/-- Every finite separated open cover equipped with exceptional inverse-image transition data
admits a normalized dualizing complex. -/
theorem nonempty {S X : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [FiniteType f]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    (HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (ωS : RingedSpace.ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
    (cover : FiniteSeparatedOpenCover f) (duality : ExceptionalInverseImageSetup f cover) :
    Nonempty (NormalizedDualizingComplexOnCover f HS HX ωS hωS cover duality) := sorry

end NormalizedDualizingComplexOnCover
end Hom
end Scheme
end AlgebraicGeometry
