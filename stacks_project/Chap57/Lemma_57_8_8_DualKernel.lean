/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap57.Lemma_57_8_2
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RelativeDualizing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.StructureSheaf
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/-- The underlying dual Fourier--Mukai kernel
`(Y ×_S X → X ×_S Y)^*(K^∨ ⊗ Lpr₂^* ω^•_{Y/S})`. -/
noncomputable def dualKernelUnderlying
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a) :
    RingedSpace.ModuleDerived (Limits.pullback g f).toRingedSpace :=
  (RingedSpace.modulePullbackDerived
    (Limits.pullbackSymmetry g f).hom.toShHom).obj
      (MonoidalCategory.tensorObj
        ((MonoidalClosed.ihomOf H K.obj).obj
          (Scheme.DerivedQCoh.structureSheaf (Limits.pullback f g)).obj)
        ((Scheme.DerivedQCoh.pullback (Limits.pullback.snd f g)).obj
          (Scheme.DerivedQCoh.relativeDualizingComplex g a aAdjunction)).obj)

/-- A perfect kernel makes the underlying dual kernel quasicoherent. -/
theorem dualKernelUnderlying_quasicoherent
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a) :
    Scheme.ModuleDerived.quasicoherentProperty (Limits.pullback g f)
      (dualKernelUnderlying f g H K a aAdjunction) := sorry

/-- The dual Fourier--Mukai kernel `K'` on `Y ×_S X`. -/
noncomputable def dualKernel
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a) :
    Scheme.DerivedQCoh (Limits.pullback g f) :=
  ⟨dualKernelUnderlying f g H K a aAdjunction,
    dualKernelUnderlying_quasicoherent f g H K hK a aAdjunction⟩

/-- Forgetting quasicoherence identifies `dualKernel` with the explicit swap-pullback formula. -/
theorem dualKernel_obj
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a) :
    (dualKernel f g H K hK a aAdjunction).obj =
      dualKernelUnderlying f g H K a aAdjunction := rfl

end AlgebraicGeometry.Scheme.FourierMukai
