/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle.Geometry

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.InvertiblePower

noncomputable section

namespace AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle

namespace TensorAction

variable {C : Type*} [Category C] [MonoidalCategory C]
variable (L E : C) [isInvertibleObject L] (h : E ⊗ L ≅ E)

/-- Iterate an actual tensor action in nonnegative degrees. -/
def nonnegative : (n : ℕ) → eval L E (n : ℤ) ≅ E
  | 0 => evalZeroIso L E
  | n + 1 =>
      evalIndexIso L E (by omega) ≪≫ (evalRightSuccIso L E n).symm ≪≫
        (nonnegative n ▷ᵢ L) ≪≫ h

/-- Undo one tensor action using full faithfulness of tensoring by the line object. -/
def predecessor (n : ℤ) (e : eval L E (n + 1) ≅ E) : eval L E n ≅ E :=
  (tensorRight L).preimageIso (evalRightSuccIso L E n ≪≫ e ≪≫ h.symm)

/-- Iterate the inverse action in negative degrees. -/
def negative : (n : ℕ) → eval L E (Int.negSucc n) ≅ E
  | 0 => predecessor L E h (Int.negSucc 0)
      (evalIndexIso L E (by omega) ≪≫ evalZeroIso L E)
  | n + 1 => predecessor L E h (Int.negSucc (n + 1))
      (evalIndexIso L E (by omega) ≪≫ negative n)

/-- The entire integer orbit is evaluated by the given actual action and its inverse. -/
def orbit : (n : ℤ) → eval L E n ≅ E
  | .ofNat n => nonnegative L E h n
  | .negSucc n => negative L E h n

/-- At weight zero the action is the identity orbit identification. -/
theorem orbit_zero : orbit L E h 0 = evalZeroIso L E := rfl

/-- In degree one the orbit uses the given multiplication, after only index and
unit identifications; it cannot substitute a zero or unrelated endomorphism. -/
theorem nonnegative_one : nonnegative L E h 1 =
    evalIndexIso L E (show (1 : ℤ) = (0 : ℤ) + 1 by omega) ≪≫
      (evalRightSuccIso L E 0).symm ≪≫ (evalZeroIso L E ▷ᵢ L) ≪≫ h := rfl

end TensorAction

variable {S X : Scheme.{u}} (f : X ⟶ S) (ℒ : X.Modules)
variable [Scheme.Modules.Invertible ℒ]
variable (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℒ))
variable [Scheme.IsRelativeSpectrumOver P]

/-- Integer powers of geometric multiplication, including inverse powers only on the
punctured bundle where its tautological section is invertible. -/
def puncturedPowerAction (p : ℕ) (n : ℤ) :
    Scheme.Modules.twistByTensorPower ℒ (puncturedAmbientForm f ℒ P p).obj n ≅
      (puncturedAmbientForm f ℒ P p).obj :=
  (Iso.refl _ ⊗ᵢ RingedSpace.InvertiblePower.categoricalIso ℒ n) ≪≫
    (evalTensorIso ℒ (puncturedAmbientForm f ℒ P p).obj n).symm ≪≫
    TensorAction.orbit ℒ (puncturedAmbientForm f ℒ P p).obj
      (asIso (tautologicalMultiplication f ℒ P p)) n

end AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle
