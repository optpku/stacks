/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.FourierMukai.RightAdjoint

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/- Lemma 57.8.7 (1): for a pseudo-coherent Fourier--Mukai kernel and a chosen right adjoint to
the second projection pushforward, the canonical Hom comparison is bijective when the target
object is perfect. -/
@[stacks 0FYW] #check
  (AlgebraicGeometry.Scheme.FourierMukai.homComparison_bijective_of_perfect_target :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HomotopyTensorDescends
      (Limits.pullback g f).toRingedSpace]
    [TensorDescends
      (Limits.pullback g f).toRingedSpace]
    [IsLocalization
      (Limits.pullback g f).toRingedSpace]
    [HomotopyTensorDescends
      (Limits.pullback f g).toRingedSpace]
    [TensorDescends
      (Limits.pullback f g).toRingedSpace]
    [IsLocalization
      (Limits.pullback f g).toRingedSpace]
    [HomotopyTensorDescends Y.toRingedSpace]
    [TensorDescends Y.toRingedSpace]
    [IsLocalization Y.toRingedSpace]
    [HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.snd f g).toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullbackSymmetry g f).inv.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullback.snd f g).toShHom)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K.obj)
    (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh (Limits.pullback f g))
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn
      (Limits.pullback.snd f g) ⊣ a)
    (M : Scheme.DerivedQCoh X) (N : Scheme.DerivedQCoh Y)
    (hN : RingedSpace.ModuleDerived.IsPerfect N.obj),
    Function.Bijective (homComparison f g H K hK a aAdjunction M N))

/- Lemma 57.8.7 (2): if the kernel is perfect and `X ⟶ S` is proper, flat, and of finite
presentation, the canonical Hom comparison is bijective for every target object. -/
@[stacks 0FYW] #check
  (AlgebraicGeometry.Scheme.FourierMukai.homComparison_bijective_of_perfect_kernel :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    [HomotopyTensorDescends
      (Limits.pullback g f).toRingedSpace]
    [TensorDescends
      (Limits.pullback g f).toRingedSpace]
    [IsLocalization
      (Limits.pullback g f).toRingedSpace]
    [HomotopyTensorDescends
      (Limits.pullback f g).toRingedSpace]
    [TensorDescends
      (Limits.pullback f g).toRingedSpace]
    [IsLocalization
      (Limits.pullback f g).toRingedSpace]
    [HomotopyTensorDescends Y.toRingedSpace]
    [TensorDescends Y.toRingedSpace]
    [IsLocalization Y.toRingedSpace]
    [HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.snd f g).toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullbackSymmetry g f).inv.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullback.snd f g).toShHom)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K.obj)
    (hK_perfect : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh (Limits.pullback f g))
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn
      (Limits.pullback.snd f g) ⊣ a)
    (M : Scheme.DerivedQCoh X) (N : Scheme.DerivedQCoh Y),
    Function.Bijective (homComparison f g H K hK a aAdjunction M N))

end AlgebraicGeometry.Scheme.FourierMukai
