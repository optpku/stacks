/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Power
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard

/-!
# Picard classes of tensor powers
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.PicardGroup

/-- The Picard class of the `n`th tensor power of an invertible module is the `n`-fold sum of
its Picard class. -/
lemma picardClass_tensorPower {X : Scheme.{u}} (M : X.Modules)
    [Scheme.Modules.Invertible M] (n : ℕ) :
    Scheme.Modules.picardClass (RingedSpace.TensorPower.sheaf M n) =
      n • Scheme.Modules.picardClass M := by
  induction n with
  | zero =>
      have hzero :
          Scheme.Modules.picardClass (RingedSpace.TensorPower.sheaf M 0) =
            Scheme.Modules.picardClass (𝟙_ X.Modules) := by
        exact (Scheme.PicardGroup.picardClass_eq_iff _ _).2 ⟨
          eqToIso (RingedSpace.TensorPower.zero M) ≪≫
            RingedSpace.unitIsoTensorUnit X.toRingedSpace⟩
      simpa using hzero.trans (Scheme.PicardGroup.picardClass_unit (X := X))
  | succ n ih =>
      have hsucc :
          Scheme.Modules.picardClass (RingedSpace.TensorPower.sheaf M (n + 1)) =
            Scheme.Modules.picardClass (M ⊗ RingedSpace.TensorPower.sheaf M n) := by
        exact (Scheme.PicardGroup.picardClass_eq_iff _ _).2 ⟨
          eqToIso (RingedSpace.TensorPower.succ M n)⟩
      calc
        Scheme.Modules.picardClass (RingedSpace.TensorPower.sheaf M (n + 1)) =
            Scheme.Modules.picardClass (M ⊗ RingedSpace.TensorPower.sheaf M n) := hsucc
        _ = Scheme.Modules.picardClass M +
              Scheme.Modules.picardClass (RingedSpace.TensorPower.sheaf M n) := by
              rw [Scheme.PicardGroup.picardClass_tensor]
        _ = Scheme.Modules.picardClass M + n • Scheme.Modules.picardClass M := by rw [ih]
        _ = (n + 1) • Scheme.Modules.picardClass M := by
              simpa [succ_nsmul, add_comm]

end AlgebraicGeometry.Scheme.PicardGroup
