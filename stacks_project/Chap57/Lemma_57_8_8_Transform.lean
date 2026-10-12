/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap57.Lemma_57_8_8_DualKernel

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/-- The Fourier--Mukai transform `Φ'` associated to the dual kernel `K'`. -/
noncomputable def dualTransform
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
    Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh X :=
  quasicoherent g f (dualKernel f g H K hK a aAdjunction)

/-- The dual transform is the Fourier--Mukai transform associated to `dualKernel`. -/
theorem dualTransform_eq
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
    dualTransform f g H K hK a aAdjunction =
      quasicoherent g f (dualKernel f g H K hK a aAdjunction) := rfl

end AlgebraicGeometry.Scheme.FourierMukai
