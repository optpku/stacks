module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.TorIndependentBaseChange

variable {X' X S' S : Scheme.{u}}

/-- For a Tor-independent cartesian base-change square whose vertical map is quasi-compact
and quasi-separated, every component of the canonical unbounded derived base-change
transformation on a derived module with quasicoherent cohomology is invertible. -/
theorem map_app_isIso
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom f'.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]
    (sq : IsPullback g' f' f g)
    (hTor : Scheme.TorIndependentOver (Over.mk f) (Over.mk g))
    (E : Scheme.ModuleDerived.Quasicoherent X) :
    IsIso ((DerivedBaseChange.map sq.toCommSq).app E.obj) := sorry

end AlgebraicGeometry.Scheme.TorIndependentBaseChange
