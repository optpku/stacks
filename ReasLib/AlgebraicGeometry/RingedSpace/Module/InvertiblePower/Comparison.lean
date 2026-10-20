/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InvertiblePower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorPower.Comparison
public import ReasLib.CategoryTheory.Monoidal.Invertible.Closed
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Coherence for integral tensor powers of invertible module sheaves

The comparisons in this file are built directly from powers of the tensor-right
autoequivalence.  In particular, they do not expose a recursive positive/dual model.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.InvertiblePower

variable {X : RingedSpace.{u}}

/-- The zeroth integral tensor power is canonically the structure module. -/
@[stacks 01CU "zeroth integral tensor power"]
noncomputable def zeroIso
    (L : Modules X) [isInvertibleObject L] :
    L ^⊗ (0 : ℤ) ≅ (SheafOfModules.unit X.ringCatSheaf : Modules X) :=
  MonoidalCategory.InvertiblePower.evalZeroIso L
    (SheafOfModules.unit X.ringCatSheaf : Modules X)

/-- Tensoring an integral tensor power on the right by `L` raises its degree by one. -/
@[stacks 01CU "right successor comparison for integral tensor powers"]
noncomputable def rightSuccIso
    (L : Modules X) [isInvertibleObject L] :
    (n : ℤ) → (L ^⊗ n) ⊗ L ≅ L ^⊗ (n + 1) :=
  MonoidalCategory.InvertiblePower.evalRightSuccIso L
    (SheafOfModules.unit X.ringCatSheaf : Modules X)

/-- Tensoring an integral tensor power on the left by `L` raises its degree by one. -/
@[stacks 01CU "left successor comparison for integral tensor powers"]
noncomputable def oneAddIso
    (L : Modules X) [isInvertibleObject L] (n : ℤ) :
    L ⊗ (L ^⊗ n) ≅ L ^⊗ (n + 1) :=
  MonoidalCategory.InvertiblePower.evalOneAddIso L
    (SheafOfModules.unit X.ringCatSheaf : Modules X) n

/-- For natural `n`, the successor natural tensor-power index agrees with integer
addition by one. -/
private theorem succSource
    (L : Modules X) [isInvertibleObject L] (n : ℕ) :
    L ^⊗ (((n + 1 : ℕ) : ℤ)) = L ^⊗ ((n : ℤ) + 1) := by
  rw [Int.natCast_succ]

/-- A positive successor power is `L` tensored with the preceding power. -/
@[stacks 01CU "positive successor comparison for integral tensor powers"]
noncomputable def succIso
    (L : Modules X) [isInvertibleObject L] (n : ℕ) :
    L ^⊗ (((n + 1 : ℕ) : ℤ)) ≅ L ⊗ (L ^⊗ (n : ℤ)) :=
  eqToIso (by rw [Int.natCast_succ]) ≪≫ (oneAddIso L (n : ℤ)).symm

/-- The recursively defined nonnegative tensor power agrees canonically with the corresponding
integral tensor power of an invertible module sheaf. -/
@[stacks 01CV "nonnegative/integral tensor-power comparison"]
noncomputable def natIso
    (L : Modules X) [isInvertibleObject L] :
    (n : ℕ) → TensorPower.sheaf L n ≅ L ^⊗ (n : ℤ)
  | 0 =>
      eqToIso (TensorPower.zero L) ≪≫ (zeroIso L).symm
  | n + 1 =>
      eqToIso (TensorPower.succ L n) ≪≫
        (Iso.refl L ⊗ᵢ natIso L n) ≪≫
          oneAddIso L (n : ℤ) ≪≫
            eqToIso ((by rw [Int.natCast_succ]) :
              L ^⊗ ((n : ℤ) + 1) = L ^⊗ (((n + 1 : ℕ) : ℤ)))

/-- The `(-1)`st tensor power is the canonical internal-Hom inverse of `L`. -/
@[stacks 01CU "inverse tensor power"]
noncomputable def negOneIso
    (L : Modules X) [isInvertibleObject L] :
    L ^⊗ (-1 : ℤ) ≅
      (ihom L).obj (SheafOfModules.unit X.ringCatSheaf : Modules X) :=
  (isInvertibleObject.inverseIsoIhom L).app
    (SheafOfModules.unit X.ringCatSheaf : Modules X)

/-- Evaluation of the canonical inverse tensor power. -/
@[stacks 01CU "evaluation of the inverse tensor power"]
noncomputable def evaluationIso
    (L : Modules X) [isInvertibleObject L] :
    L ⊗ (L ^⊗ (-1 : ℤ)) ≅
      (SheafOfModules.unit X.ringCatSheaf : Modules X) :=
  oneAddIso L (-1 : ℤ) ≪≫ zeroIso L

/-- Evaluation with the canonical inverse tensor power on the left. -/
@[stacks 01CU "right evaluation of the inverse tensor power"]
noncomputable def rightEvaluationIso
    (L : Modules X) [isInvertibleObject L] :
    (L ^⊗ (-1 : ℤ)) ⊗ L ≅
      (SheafOfModules.unit X.ringCatSheaf : Modules X) :=
  rightSuccIso L (-1) ≪≫ zeroIso L

/-- Tensoring by the canonical inverse power lowers the degree by one. -/
@[stacks 01CU "predecessor comparison for integral tensor powers"]
noncomputable def minusOneAddIso
    (L : Modules X) [isInvertibleObject L] (n : ℤ) :
    (L ^⊗ (-1 : ℤ)) ⊗ (L ^⊗ n) ≅ L ^⊗ (n - 1) :=
  (categoricalIso L (-1) ⊗ᵢ categoricalIso L n) ≪≫
    MonoidalCategory.InvertiblePower.minusOneAddIso L n ≪≫
    (categoricalIso L (n - 1)).symm

/-- Each further negative power is the `(-1)`st power tensored with the preceding one. -/
@[stacks 01CU "negative successor comparison for integral tensor powers"]
noncomputable def negSuccPowerIso
    (L : Modules X) [isInvertibleObject L] (n : ℕ) :
    L ^⊗ Int.negSucc (n + 1) ≅
      (L ^⊗ (-1 : ℤ)) ⊗ (L ^⊗ Int.negSucc n) :=
  categoricalIso L (Int.negSucc (n + 1)) ≪≫
    MonoidalCategory.InvertiblePower.negSuccIso L n ≪≫
    ((categoricalIso L (-1)).symm ⊗ᵢ
      (categoricalIso L (Int.negSucc n)).symm)

/-- Each further negative power is the internal-Hom inverse tensored with the preceding one. -/
@[stacks 01CU "negative successor via internal Hom"]
noncomputable def negSuccIso
    (L : Modules X) [isInvertibleObject L] (n : ℕ) :
    L ^⊗ Int.negSucc (n + 1) ≅
      (ihom L).obj (SheafOfModules.unit X.ringCatSheaf : Modules X) ⊗
        (L ^⊗ Int.negSucc n) :=
  negSuccPowerIso L n ≪≫
    (negOneIso L ⊗ᵢ Iso.refl (L ^⊗ Int.negSucc n))

/-- Tensoring powers of `L` adds their integer degrees. -/
@[stacks 01CU "addition comparison for integral tensor powers"]
noncomputable def addIso
    (L : Modules X) [isInvertibleObject L] (m n : ℤ) :
    (L ^⊗ m) ⊗ (L ^⊗ n) ≅ L ^⊗ (m + n) :=
  (categoricalIso L m ⊗ᵢ categoricalIso L n) ≪≫
    MonoidalCategory.InvertiblePower.addIso L m n ≪≫
    (categoricalIso L (m + n)).symm

/-- The integral tensor-power addition comparison is associative. -/
theorem addIso_assoc
    (L : Modules X) [isInvertibleObject L] (m n k : ℤ) :
    (addIso L m n ▷ᵢ (L ^⊗ k)) ≪≫ addIso L (m + n) k =
      α_ (L ^⊗ m) (L ^⊗ n) (L ^⊗ k) ≪≫
        (Iso.refl (L ^⊗ m) ⊗ᵢ addIso L n k) ≪≫
        addIso L m (n + k) ≪≫ indexIso L (Int.add_assoc m n k).symm := sorry

/-- The integral tensor-power addition comparison is compatible with symmetry. -/
theorem addIso_braiding
    (L : Modules X) [isInvertibleObject L] (m n : ℤ) :
    β_ (L ^⊗ m) (L ^⊗ n) ≪≫ addIso L n m ≪≫
        indexIso L (Int.add_comm n m) =
      addIso L m n := sorry

end AlgebraicGeometry.RingedSpace.InvertiblePower
