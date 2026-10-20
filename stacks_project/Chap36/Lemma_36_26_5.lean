/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.InternalHomPushforward.Flat

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.ModuleDerived
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 36.26.5 (1): if `f` is quasi-compact and quasi-separated, `E` is perfect, and
`G` is bounded above with quasi-coherent terms flat over `S`, then the canonical comparison
from `Lg^* Rf_* RHom(E, Q(G))` to the corresponding base-changed internal Hom formed using
the ordinary termwise pullback of `G` is an isomorphism. -/
@[stacks 08IE] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardInternalHomBaseChange_isIso_of_isPerfect :
  ∀ {X' X S' S : Scheme.{u}}
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
    [Fact (RingedSpace.ModuleDerived.IsPerfect E)]
    (G : CochainComplex X.Modules ℤ)
    [Fact (CochainComplex.minus X.Modules G)]
    [∀ n : ℤ, (G.X n).IsQuasicoherent]
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom],
    IsIso
      (internalHomPushforwardBaseChangeMap g' f' f g sq H_X H_X' E G))

/- Lemma 36.26.5 (2): if `f` is quasi-compact and quasi-separated, `E` is
pseudo-coherent, and `G` is bounded with quasi-coherent terms flat over `S`, then the
canonical comparison from `Lg^* Rf_* RHom(E, Q(G))` to the corresponding base-changed
internal Hom formed using the ordinary termwise pullback of `G` is an isomorphism. -/
@[stacks 08IE] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardInternalHomBaseChange_isIso_of_isPseudoCoherent :
  ∀ {X' X S' S : Scheme.{u}}
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
    [Fact (RingedSpace.ModuleDerived.IsPseudoCoherent E)]
    (G : CochainComplex X.Modules ℤ)
    [Fact (CochainComplex.bounded X.Modules G)]
    [∀ n : ℤ, (G.X n).IsQuasicoherent]
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom],
    IsIso
      (internalHomPushforwardBaseChangeMap g' f' f g sq H_X H_X' E G))

end AlgebraicGeometry.Scheme.DerivedQCoh

end
