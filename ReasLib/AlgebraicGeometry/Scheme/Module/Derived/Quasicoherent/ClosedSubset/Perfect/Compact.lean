module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Compact
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ClosedSubset.Generation
public import ReasLib.CategoryTheory.Pretriangulated.CompactObject.Generation

/-!
# Compact and perfect complexes with closed support

Compact objects in the derived category of quasicoherent modules supported on a closed subset
with quasi-compact complement are characterized by perfectness.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn

/-- Let `X` be a quasi-compact and quasi-separated scheme, and let `T` be a closed subset of `X`
whose complement is quasi-compact. An object of the derived category of quasicoherent modules on
`X` supported on `T` is compact if and only if its underlying derived module is perfect. -/
@[stacks 0A9B]
theorem isCompactObject_iff_isPerfect {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (T : TopologicalSpace.Closeds X)
    (hT : IsCompact (T.compl : Set X)) (E : SupportedOn X T) :
    IsCompactObject E ↔ RingedSpace.ModuleDerived.IsPerfect E.obj.obj := sorry

/-- Let `X` be a quasi-compact and quasi-separated scheme, and let `T` be a closed subset of `X`
whose complement is quasi-compact. An object of the derived category of quasicoherent modules on
`X` supported on `T` is compact if its underlying derived module is perfect. -/
theorem isCompactObject_of_isPerfect {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (T : TopologicalSpace.Closeds X)
    (hT : IsCompact (T.compl : Set X)) {E : SupportedOn X T}
    (hE : RingedSpace.ModuleDerived.IsPerfect E.obj.obj) : IsCompactObject E := sorry

/-- Let `X` be a quasi-compact and quasi-separated scheme, and let `T` be a closed subset of `X`
whose complement is quasi-compact. A compact object of the derived category of quasicoherent
modules on `X` supported on `T` has a perfect underlying derived module. -/
theorem isPerfect_of_isCompactObject {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (T : TopologicalSpace.Closeds X)
    (hT : IsCompact (T.compl : Set X)) {E : SupportedOn X T}
    (hE : IsCompactObject E) : RingedSpace.ModuleDerived.IsPerfect E.obj.obj := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn
