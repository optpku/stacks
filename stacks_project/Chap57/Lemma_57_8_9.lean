/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.FourierMukai.Adjunction

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpace.ModuleDerived.KFlat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/- Lemma 57.8.9 (1): if `S` is Noetherian and `X`, `Y` are proper and flat over `S`,
a perfect kernel on `X ×_S Y` induces a Fourier--Mukai functor
`Φ_K : D_perf(𝒪_X) ⟶ D_perf(𝒪_Y)`. -/
@[stacks 0FYY] #check
  (AlgebraicGeometry.Scheme.FourierMukai.perfectNoetherian :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [IsProper f] [Flat f] [IsProper g] [Flat g]
    (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback f g).toRingedSpace),
    @RingedSpace.ModuleDerived.Perfect X.toRingedSpace ⥤
      @RingedSpace.ModuleDerived.Perfect Y.toRingedSpace)

/- Lemma 57.8.9 (2): composition of perfect Fourier--Mukai transforms is naturally
isomorphic to the transform of the perfect convolution kernel. -/
@[stacks 0FYY] #check
  (AlgebraicGeometry.Scheme.FourierMukai.perfect_composition_iso_convolution :
    ∀ {S X Y Z T : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    [IsNoetherian S]
    [IsProper f] [Flat f] [IsProper g] [Flat g] [IsProper h] [Flat h]
    (p12 : T ⟶ Limits.pullback f g)
    (p23 : T ⟶ Limits.pullback g h)
    (p13 : T ⟶ Limits.pullback f h)
    (hT : IsPullback p12 p23 (Limits.pullback.snd f g) (Limits.pullback.fst g h))
    (h_p13_x : p13 ≫ Limits.pullback.fst f h = p12 ≫ Limits.pullback.fst f g)
    (h_p13_z : p13 ≫ Limits.pullback.snd f h = p23 ≫ Limits.pullback.snd g h)
    (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback f g).toRingedSpace)
    (K' : @RingedSpace.ModuleDerived.Perfect (Limits.pullback g h).toRingedSpace),
    Nonempty ((perfectNoetherian f g K ⋙ perfectNoetherian g h K') ≅
      perfectNoetherian f h
        (perfectConvolutionKernel f g h p12 p23 p13 hT h_p13_x h_p13_z K K')))

/- Lemma 57.8.9 (3): the pr₁ dualizing kernel gives the specified right adjoint
when the source morphism is Gorenstein. -/
@[stacks 0FYY] #check
  (AlgebraicGeometry.Scheme.FourierMukai.perfectNoetherian_rightAdjunction :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [IsProper f] [IsProper g] [Flat g]
    [AlgebraicGeometry.Gorenstein f]
    [HomotopyTensorDescends (Limits.pullback f g).toRingedSpace]
    [TensorDescends (Limits.pullback f g).toRingedSpace]
    [IsLocalization (Limits.pullback f g).toRingedSpace]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback f g).toRingedSpace)
    (hK : Scheme.ModuleDerived.quasicoherentProperty (Limits.pullback f g) K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh X)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a),
    Nonempty (perfectNoetherian f g K ⊣
      perfectNoetherian g f (perfectRightKernel f g H K hK a aAdjunction)))

/- Lemma 57.8.9 (4): the pr₂ dualizing kernel gives the specified left adjoint
when the target morphism is Gorenstein. -/
@[stacks 0FYY] #check
  (AlgebraicGeometry.Scheme.FourierMukai.perfectNoetherian_leftAdjunction :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [IsProper f] [Flat f] [IsProper g]
    [AlgebraicGeometry.Gorenstein g]
    [HomotopyTensorDescends (Limits.pullback f g).toRingedSpace]
    [TensorDescends (Limits.pullback f g).toRingedSpace]
    [IsLocalization (Limits.pullback f g).toRingedSpace]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback f g).toRingedSpace)
    (hK : Scheme.ModuleDerived.quasicoherentProperty (Limits.pullback f g) K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a),
    Nonempty (perfectNoetherian g f (perfectLeftKernel f g H K hK a aAdjunction) ⊣
      perfectNoetherian f g K))

end AlgebraicGeometry.Scheme.FourierMukai
