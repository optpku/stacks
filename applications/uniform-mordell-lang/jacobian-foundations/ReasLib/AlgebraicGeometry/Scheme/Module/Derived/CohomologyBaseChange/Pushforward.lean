module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.Criteria

/-!
# Cohomology and base change for derived pushforwards

This module promotes pointwise cohomology base-change isomorphisms to an isomorphism
between derived pushforwards.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Hom RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For a cartesian square of schemes whose vertical morphism is quasi-compact and
quasi-separated, pointwise cohomology base-change isomorphisms make the composite of
canonical derived base change with the pushed-forward comparison morphism invertible. -/
theorem cohomologyBaseChange_comp_isIso
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [RingedSpace.DerivedAdjunction.HasPair f.toShHom]
    [RingedSpace.DerivedAdjunction.HasPair f'.toShHom]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]
    (sq : IsPullback g' f' f g) (K : ModuleDerived.Quasicoherent X)
    (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K')
    [∀ (x' : X') (i : ℤ),
      IsIso ((CohomologyBaseChangeModel.canonical g' f' f g sq).pointMap K K' α x' i)] :
    IsIso
      ((DerivedBaseChange.map sq.toCommSq).app K.obj ≫
        (RingedSpace.moduleDerivedPushforward f'.toShHom).map
          ((pullback.inclusionIso g').inv.app K ≫
            (ModuleDerived.Quasicoherent.inclusion X').map α)) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh

end
