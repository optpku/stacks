module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ClosedSubset.Closure
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ClosedSubset.Coproduct
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ClosedSubset.Perfect.Compact

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn

/-- On a quasi-compact quasi-separated scheme, a perfect weak generator of the derived
category of quasi-coherent modules supported on a closed subset with quasi-compact complement
classically generates its compact objects. -/
theorem isClassicalGeneratorOfCompacts {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (T : TopologicalSpace.Closeds X)
    (hT : IsCompact (T.compl : Set X)) (G : SupportedOn X T)
    (hG_perfect : RingedSpace.ModuleDerived.IsPerfect G.obj.obj)
    (hG_generator : IsWeakGenerator G) :
    IsClassicalGeneratorOfCompacts G := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn
