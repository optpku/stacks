/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap57.Lemma_57_8_8_DualKernel
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/-- The underlying right-adjoint Fourier--Mukai kernel
`(Y ×_S X → X ×_S Y)^*(Lpr₁^* ω^•_{X/S} ⊗ K^∨)`. -/
noncomputable def dualKernelOfPr1Underlying
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)]
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
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)]
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
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)]
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
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)]
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
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [AlgebraicGeometry.Gorenstein f]
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)]
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
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [AlgebraicGeometry.Gorenstein g]
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a) :
    RingedSpace.ModuleDerived.IsPerfect
      (dualKernel f g H K hK a aAdjunction).obj := sorry

end AlgebraicGeometry.Scheme.FourierMukai
