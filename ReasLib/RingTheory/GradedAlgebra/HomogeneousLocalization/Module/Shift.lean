/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Graded.Shift.NatInt
public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Away.Module

/-!
# Grading shifts after homogeneous localization

Multiplication by an integral power of the inverted homogeneous element compares degree-zero
homogeneous localizations of a graded module and its translated grading.
-/

@[expose] public section

noncomputable section

universe u

namespace HomogeneousLocalization.Away.Module

variable {A M : Type u} [CommRing A]
variable [AddCommGroup M] [Module A M]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule ℤ M) [SetLike.GradedSMul 𝒜 ℳ]

/-- Multiplication by the `n`-th integral power of an inverted homogeneous element sends the
degree-zero localization of `ℳ` to that of the grading translated by `n * d`. -/
noncomputable def shiftAction {d : ℕ} (f : 𝒜 d) (n : ℤ) :
    degreeZeroPart 𝒜 (HomogeneousLocalization.Module.nonnegativeGrading ℳ) f →ₗ[
      HomogeneousLocalization.Away 𝒜 (f : A)]
        degreeZeroPart 𝒜 (HomogeneousLocalization.Module.nonnegativeGrading
          (GradedModule.shiftGrading ℳ (n * (d : ℤ)))) f where
  toFun x :=
    ⟨((((IsLocalization.Away.algebraMap_isUnit (f : A)).unit ^ n :
          (Localization.Away (f : A))ˣ) : Localization.Away (f : A)) •
        (x : LocalizedModule.Away (f : A) M)), sorry⟩
  map_add' x y := by
    ext
    exact smul_add _ _ _
  map_smul' r x := by
    ext
    let u : Localization.Away (f : A) :=
      (((IsLocalization.Away.algebraMap_isUnit (f : A)).unit ^ n :
        (Localization.Away (f : A))ˣ) : Localization.Away (f : A))
    change u • (r.val • (x : LocalizedModule.Away (f : A) M)) =
      r.val • (u • (x : LocalizedModule.Away (f : A) M))
    rw [← smul_assoc, ← smul_assoc, smul_eq_mul, smul_eq_mul, mul_comm]

/-- The shift comparison acts on the ordinary localized module by multiplication by `f^n`. -/
theorem shiftAction_val {d : ℕ} (f : 𝒜 d) (n : ℤ)
    (x : degreeZeroPart 𝒜 (HomogeneousLocalization.Module.nonnegativeGrading ℳ) f) :
    (shiftAction 𝒜 ℳ f n x : LocalizedModule.Away (f : A) M) =
      ((((IsLocalization.Away.algebraMap_isUnit (f : A)).unit ^ n :
          (Localization.Away (f : A))ˣ) : Localization.Away (f : A)) •
        (x : LocalizedModule.Away (f : A) M)) := rfl

/-- Multiplication by an integral power of the inverted homogeneous element is a bijection
between the corresponding degree-zero homogeneous localizations. -/
theorem shiftAction_bijective {d : ℕ} (f : 𝒜 d) (n : ℤ) :
    Function.Bijective (shiftAction 𝒜 ℳ f n) := sorry

end HomogeneousLocalization.Away.Module
