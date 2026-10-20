/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.FourierMukai.LeftAdjoint

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/- Lemma 57.8.8: the swapped dual kernel twisted by the relative dualizing complex,
its quasicoherence certificate, and its underlying-object computation. -/
#check
  (AlgebraicGeometry.Scheme.FourierMukai.dualKernelUnderlying :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a),
    RingedSpace.ModuleDerived (Limits.pullback g f).toRingedSpace)

#check
  (AlgebraicGeometry.Scheme.FourierMukai.dualKernelUnderlying_quasicoherent :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a),
    Scheme.ModuleDerived.quasicoherentProperty (Limits.pullback g f)
      (dualKernelUnderlying f g H K a aAdjunction))

#check
  (AlgebraicGeometry.Scheme.FourierMukai.dualKernel :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a),
    Scheme.DerivedQCoh (Limits.pullback g f))

#check
  (AlgebraicGeometry.Scheme.FourierMukai.dualKernel_obj :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a),
    (dualKernel f g H K hK a aAdjunction).obj =
      dualKernelUnderlying f g H K a aAdjunction)

end AlgebraicGeometry.Scheme.FourierMukai
