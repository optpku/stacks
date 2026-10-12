/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.InternalHomPushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.InternalHom
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.TensorPushforward.Flat

/-!
# Flat base change for internal Hom and derived pushforward

This module proves invertibility of the internal-Hom pushforward base-change comparison for
degreewise quasicoherent coefficient complexes that are flat over the base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.DerivedCategory
open AlgebraicGeometry.RingedSpace.ModuleDerived
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For a cartesian square and a quasi-compact, quasi-separated vertical morphism, the
internal-Hom pushforward base-change map is an isomorphism when its first argument is perfect
and its coefficient complex is bounded above, degreewise quasicoherent, and flat over the
base. -/
instance pushforwardInternalHomBaseChange_isIso_of_isPerfect
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [KFlat.HomotopyTensorDescends X'.toRingedSpace]
    [KFlat.TensorDescends X'.toRingedSpace]
    [KFlat.IsLocalization X'.toRingedSpace]
    [DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.toShHom)]
    [DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f'.toShHom)]
    [IsIso
      (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
    [IsIso
      (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]
    [(RingedSpace.modulePullbackDerived g'.toShHom).Monoidal]
    (sq : IsPullback g' f' f g)
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    [hE : Fact (RingedSpace.ModuleDerived.IsPerfect E)]
    (G : CochainComplex X.Modules ℤ)
    [Fact (CochainComplex.minus X.Modules G)]
    [∀ n : ℤ, (G.X n).IsQuasicoherent]
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom] :
    IsIso
      (internalHomPushforwardBaseChangeMap g' f' f g sq H_X H_X' E G) := sorry

/-- For a cartesian square and a quasi-compact, quasi-separated vertical morphism, the
internal-Hom pushforward base-change map is an isomorphism when its first argument is
pseudo-coherent and its coefficient complex is bounded, degreewise quasicoherent, and flat
over the base. -/
instance pushforwardInternalHomBaseChange_isIso_of_isPseudoCoherent
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [KFlat.HomotopyTensorDescends X'.toRingedSpace]
    [KFlat.TensorDescends X'.toRingedSpace]
    [KFlat.IsLocalization X'.toRingedSpace]
    [DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.toShHom)]
    [DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f'.toShHom)]
    [IsIso
      (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
    [IsIso
      (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]
    [(RingedSpace.modulePullbackDerived g'.toShHom).Monoidal]
    (sq : IsPullback g' f' f g)
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    [hE : Fact (RingedSpace.ModuleDerived.IsPseudoCoherent E)]
    (G : CochainComplex X.Modules ℤ)
    [Fact (CochainComplex.bounded X.Modules G)]
    [∀ n : ℤ, (G.X n).IsQuasicoherent]
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom] :
    IsIso
      (internalHomPushforwardBaseChangeMap g' f' f g sq H_X H_X' E G) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh

end
