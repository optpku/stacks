/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.FourierMukai.LeftAdjoint

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/- Lemma 57.8.8: over a Noetherian scheme `S`, if `Y ⟶ S` is flat proper Gorenstein and
`X ⟶ S` is of finite type, the transform with kernel
`swap^*(K^∨ ⊗ Lpr₂^* ω^•_{Y/S})` is left adjoint to the transform with perfect kernel `K`.
Its inverse adjunction Hom equivalence gives the canonical isomorphism
`Hom_Y(N, Φ(M)) ≅ Hom_X(Φ'(N), M)`, functorial in both objects. -/
@[stacks 0FYX] #check
  (AlgebraicGeometry.Scheme.FourierMukai.dualTransform_nonempty_adjunction :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S]
    [IsProper g] [Flat g] [AlgebraicGeometry.Gorenstein g]
    [LocallyOfFiniteType f]
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HomotopyTensorDescends (Limits.pullback g f).toRingedSpace]
    [TensorDescends (Limits.pullback g f).toRingedSpace]
    [IsLocalization (Limits.pullback g f).toRingedSpace]
    [HomotopyTensorDescends (Limits.pullback f g).toRingedSpace]
    [TensorDescends (Limits.pullback f g).toRingedSpace]
    [IsLocalization (Limits.pullback f g).toRingedSpace]
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.fst f g).toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullback.fst f g).toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullbackSymmetry g f).hom.toShHom)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    [CompactSpace (Limits.pullback f g : Scheme.{u})]
    [QuasiSeparatedSpace (Limits.pullback f g : Scheme.{u})]
    [CompactSpace (Limits.pullback g f : Scheme.{u})]
    [QuasiSeparatedSpace (Limits.pullback g f : Scheme.{u})]
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a),
    Nonempty (dualTransform f g H K hK a aAdjunction ⊣ quasicoherent f g K))

end AlgebraicGeometry.Scheme.FourierMukai
