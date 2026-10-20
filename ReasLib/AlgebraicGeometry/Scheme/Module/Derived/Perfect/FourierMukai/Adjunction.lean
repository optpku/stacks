/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.FourierMukai
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.FourierMukai.LeftAdjoint
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open RingedSpace.ModuleDerived.KFlat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/-- The underlying right-adjoint Fourier--Mukai kernel
`(Y ×_S X → X ×_S Y)^*(Lpr₁^* ω^•_{X/S} ⊗ K^∨)`. -/
noncomputable def dualKernelOfPr1Underlying
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [HomotopyTensorDescends (Limits.pullback f g).toRingedSpace]
    [TensorDescends (Limits.pullback f g).toRingedSpace]
    [IsLocalization (Limits.pullback f g).toRingedSpace]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh X)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a) :
    RingedSpace.ModuleDerived (Limits.pullback g f).toRingedSpace :=
  (RingedSpace.modulePullbackDerived
    (Limits.pullbackSymmetry g f).hom.toShHom).obj
      (MonoidalCategory.tensorObj
        ((Scheme.DerivedQCoh.pullback (Limits.pullback.fst f g)).obj
          (Scheme.DerivedQCoh.relativeDualizingComplex f a aAdjunction)).obj
        ((MonoidalClosed.ihomOf H K.obj).obj
          (Scheme.DerivedQCoh.structureSheaf (Limits.pullback f g)).obj))

/-- A perfect kernel makes the underlying pr₁ dual kernel quasicoherent. -/
theorem dualKernelOfPr1Underlying_quasicoherent
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [HomotopyTensorDescends (Limits.pullback f g).toRingedSpace]
    [TensorDescends (Limits.pullback f g).toRingedSpace]
    [IsLocalization (Limits.pullback f g).toRingedSpace]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh X)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a) :
    Scheme.ModuleDerived.quasicoherentProperty (Limits.pullback g f)
      (dualKernelOfPr1Underlying f g H K a aAdjunction) := sorry

/-- The right-adjoint Fourier--Mukai kernel on `Y ×_S X` associated to `pr₁` and
the relative dualizing complex of `X ⟶ S`. -/
noncomputable def dualKernelOfPr1
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [HomotopyTensorDescends (Limits.pullback f g).toRingedSpace]
    [TensorDescends (Limits.pullback f g).toRingedSpace]
    [IsLocalization (Limits.pullback f g).toRingedSpace]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh X)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a) :
    Scheme.DerivedQCoh (Limits.pullback g f) :=
  ⟨dualKernelOfPr1Underlying f g H K a aAdjunction,
    dualKernelOfPr1Underlying_quasicoherent f g H K hK a aAdjunction⟩

/-- Forgetting quasicoherence identifies `dualKernelOfPr1` with the explicit
swap-pullback formula. -/
theorem dualKernelOfPr1_obj
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [HomotopyTensorDescends (Limits.pullback f g).toRingedSpace]
    [TensorDescends (Limits.pullback f g).toRingedSpace]
    [IsLocalization (Limits.pullback f g).toRingedSpace]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh X)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a) :
    (dualKernelOfPr1 f g H K hK a aAdjunction).obj =
      dualKernelOfPr1Underlying f g H K a aAdjunction := rfl

/-- Under Gorenstein hypotheses on `X ⟶ S`, the pr₁ dual kernel is perfect. -/
theorem dualKernelOfPr1_isPerfect
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [IsProper f] [IsProper g] [Flat g]
    [AlgebraicGeometry.Gorenstein f]
    [HomotopyTensorDescends (Limits.pullback f g).toRingedSpace]
    [TensorDescends (Limits.pullback f g).toRingedSpace]
    [IsLocalization (Limits.pullback f g).toRingedSpace]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh X)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a) :
    RingedSpace.ModuleDerived.IsPerfect
      (dualKernelOfPr1 f g H K hK a aAdjunction).obj := sorry

/-- Under Gorenstein hypotheses on `Y ⟶ S`, the pr₂ dual kernel is perfect. -/
theorem dualKernel_isPerfect
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [IsProper f] [Flat f] [IsProper g]
    [AlgebraicGeometry.Gorenstein g]
    [HomotopyTensorDescends (Limits.pullback f g).toRingedSpace]
    [TensorDescends (Limits.pullback f g).toRingedSpace]
    [IsLocalization (Limits.pullback f g).toRingedSpace]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a) :
    RingedSpace.ModuleDerived.IsPerfect
      (dualKernel f g H K hK a aAdjunction).obj := sorry

/-- The perfect right-adjoint kernel is the swapped dual kernel twisted by the
relative dualizing complex of the source Gorenstein morphism. -/
noncomputable def perfectRightKernel
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
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
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a) :
    @RingedSpace.ModuleDerived.Perfect (Limits.pullback g f).toRingedSpace :=
  ⟨(dualKernelOfPr1 f g H ⟨K.obj, hK⟩ K.property a aAdjunction).obj,
    dualKernelOfPr1_isPerfect f g H ⟨K.obj, hK⟩ K.property a aAdjunction⟩

/-- The underlying object of the perfect right-adjoint kernel is the explicit
swapped dualizing twist of the original kernel. -/
theorem perfectRightKernel_obj
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
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
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a) :
    (perfectRightKernel f g H K hK a aAdjunction).obj =
      dualKernelOfPr1Underlying f g H ⟨K.obj, hK⟩ a aAdjunction := rfl

/-- The perfect left-adjoint kernel is the swapped dual kernel twisted by the
relative dualizing complex of the target Gorenstein morphism. -/
noncomputable def perfectLeftKernel
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
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
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a) :
    @RingedSpace.ModuleDerived.Perfect (Limits.pullback g f).toRingedSpace :=
  ⟨(dualKernel f g H ⟨K.obj, hK⟩ K.property a aAdjunction).obj,
    dualKernel_isPerfect f g H ⟨K.obj, hK⟩ K.property a aAdjunction⟩

/-- The underlying object of the perfect left-adjoint kernel is the explicit
swapped dualizing twist of the original kernel. -/
theorem perfectLeftKernel_obj
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
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
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a) :
    (perfectLeftKernel f g H K hK a aAdjunction).obj =
      dualKernelUnderlying f g H ⟨K.obj, hK⟩ a aAdjunction := rfl

/-- For a Gorenstein source, the transform of the specified perfect dualizing kernel
is right adjoint to the original perfect Fourier–Mukai transform. -/
theorem perfectNoetherian_rightAdjunction
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
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
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a) :
    Nonempty (perfectNoetherian f g K ⊣
      perfectNoetherian g f (perfectRightKernel f g H K hK a aAdjunction)) := sorry

/-- For a Gorenstein target, the transform of the specified perfect dualizing kernel
is left adjoint to the original perfect Fourier–Mukai transform. -/
theorem perfectNoetherian_leftAdjunction
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
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
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a) :
    Nonempty (perfectNoetherian g f (perfectLeftKernel f g H K hK a aAdjunction) ⊣
      perfectNoetherian f g K) := sorry

/-- The perfect transform of the source dualizing kernel is a right adjoint. -/
instance instIsRightAdjoint_perfectNoetherian_dualKernelOfPr1
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
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
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a) :
    (perfectNoetherian g f (perfectRightKernel f g H K hK a aAdjunction)).IsRightAdjoint where
  exists_leftAdjoint := ⟨perfectNoetherian f g K,
    perfectNoetherian_rightAdjunction f g H K hK a aAdjunction⟩

/-- The perfect transform of the target dualizing kernel is a left adjoint. -/
instance instIsLeftAdjoint_perfectNoetherian_dualKernel
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
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
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a) :
    (perfectNoetherian g f (perfectLeftKernel f g H K hK a aAdjunction)).IsLeftAdjoint where
  exists_rightAdjoint := ⟨perfectNoetherian f g K,
    perfectNoetherian_leftAdjunction f g H K hK a aAdjunction⟩

end AlgebraicGeometry.Scheme.FourierMukai
