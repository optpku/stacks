/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.TensorPushforward.Flat

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.DerivedCategory
open AlgebraicGeometry.RingedSpace.ModuleDerived
open DerivedTensor.Right.Monoidal
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 36.26.4: for a quasi-compact and quasi-separated morphism `f`, a derived
quasi-coherent object `E`, and a bounded-above degreewise quasi-coherent complex `G` flat over
the base, the canonical morphism from `Lg^* Rf_*(E ⊗ᴸ Q(G))` to the base-changed pushforward
formed using the ordinary termwise pullback of `G` is an isomorphism. -/
@[stacks 0A1D] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardTensorBaseChange_isIso :
  ∀ {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [KFlat.HomotopyTensorDescends X'.toRingedSpace]
    [KFlat.TensorDescends X'.toRingedSpace]
    [KFlat.IsLocalization X'.toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom f'.toShHom)]
    [IsIso
      (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
    [IsIso
      (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]
    [(RingedSpace.modulePullbackDerived g'.toShHom).Monoidal]
    (sq : IsPullback g' f' f g)
    (T_X : @Model
      (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _ _ _)
    (T_X' : @Model
      (RingedSpace.Modules X'.toRingedSpace) _ _ _ _ _ _ _)
    (E : ModuleDerived.Quasicoherent X) (G : CochainComplex X.Modules ℤ)
    [hG_bounded : Fact (CochainComplex.minus X.Modules G)]
    [∀ n : ℤ, (G.X n).IsQuasicoherent]
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom],
    IsIso (tensorPushforwardBaseChangeMap g' f' f g sq T_X T_X' E G))

end AlgebraicGeometry.Scheme.DerivedQCoh

end
