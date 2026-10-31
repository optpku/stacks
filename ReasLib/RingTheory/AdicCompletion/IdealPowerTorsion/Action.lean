/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.RingTheory.AdicCompletion.Evaluation

@[expose] public section

noncomputable section

universe u v

namespace Ideal.PowerAnnihilated

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The action of a quotient scalar on an element annihilated by the corresponding
power of the ideal, viewed in the ambient module. -/
def quotientAction (I : Ideal R) (n : ℕ) (a : R ⧸ I ^ n)
    (x : I.powerAnnihilatedSubmodule M n) : M :=
  ((a • x : I.powerAnnihilatedSubmodule M n) : M)

/-- The finite-stage quotient action of the class of `r` agrees with the original
`R`-action. -/
theorem quotientAction_mk (I : Ideal R) (n : ℕ) (r : R)
    (x : I.powerAnnihilatedSubmodule M n) :
    quotientAction I n (Ideal.Quotient.mk (I ^ n) r) x = r • x := by
  rfl

private theorem quotientAction_eval_eq_of_le (I : Ideal R) (a : AdicCompletion I R)
    (x : M) {m n : ℕ} (hmn : m ≤ n)
    (hm : x ∈ I.powerAnnihilatedSubmodule M m)
    (hn : x ∈ I.powerAnnihilatedSubmodule M n) :
    quotientAction I m (AdicCompletion.evalₐ I m a) ⟨x, hm⟩ =
      quotientAction I n (AdicCompletion.evalₐ I n a) ⟨x, hn⟩ := by
  induction a using AdicCompletion.induction_on with
  | _ f =>
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk,
      ← AdicCompletion.Ideal.mk_eq_mk I hmn f, quotientAction_mk, quotientAction_mk]

private theorem quotientAction_eval_eq (I : Ideal R) (a : AdicCompletion I R)
    (x : M) {m n : ℕ} (hm : x ∈ I.powerAnnihilatedSubmodule M m)
    (hn : x ∈ I.powerAnnihilatedSubmodule M n) :
    quotientAction I m (AdicCompletion.evalₐ I m a) ⟨x, hm⟩ =
      quotientAction I n (AdicCompletion.evalₐ I n a) ⟨x, hn⟩ := by
  rcases le_total m n with hmn | hnm
  · exact quotientAction_eval_eq_of_le I a x hmn hm hn
  · exact (quotientAction_eval_eq_of_le I a x hnm hn hm).symm

end Ideal.PowerAnnihilated

namespace Module.IsIdealPowerTorsion

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The underlying action of a completed scalar on an ideal-power-torsion element. -/
noncomputable def completionAction (I : Ideal R)
    (hM : Module.IsIdealPowerTorsion I M) (a : AdicCompletion I R) (x : M) : M :=
  let hx : x ∈ Ideal.primaryComponent M I := by
    rw [hM]
    exact Submodule.mem_top
  let hx := (Ideal.primaryComponent_mem M I x).mp hx
  let n := Classical.choose hx
  Ideal.PowerAnnihilated.quotientAction I n (AdicCompletion.evalₐ I n a)
    ⟨x, Classical.choose_spec hx⟩

private theorem completionAction_eq_of_mem_stage (I : Ideal R)
    (hM : Module.IsIdealPowerTorsion I M) (a : AdicCompletion I R)
    (n : ℕ) (x : M) (hx : x ∈ I.powerAnnihilatedSubmodule M n) :
    completionAction I hM a x =
      Ideal.PowerAnnihilated.quotientAction I n (AdicCompletion.evalₐ I n a) ⟨x, hx⟩ := by
  dsimp only [completionAction]
  exact Ideal.PowerAnnihilated.quotientAction_eval_eq I a x _ hx

/-- The completed-scalar action is additive in the module argument. -/
theorem completionAction_add (I : Ideal R)
    (hM : Module.IsIdealPowerTorsion I M) (a : AdicCompletion I R) (x y : M) :
    completionAction I hM a (x + y) =
      completionAction I hM a x + completionAction I hM a y := by
  obtain ⟨m, hm⟩ := (Ideal.primaryComponent_mem M I x).mp (by
    rw [hM]
    exact Submodule.mem_top)
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I y).mp (by
    rw [hM]
    exact Submodule.mem_top)
  have hx : x ∈ I.powerAnnihilatedSubmodule M (max m n) :=
    Submodule.torsionBySet_le_torsionBySet_pow m (max m n) (le_max_left _ _) I hm
  have hy : y ∈ I.powerAnnihilatedSubmodule M (max m n) :=
    Submodule.torsionBySet_le_torsionBySet_pow n (max m n) (le_max_right _ _) I hn
  rw [completionAction_eq_of_mem_stage I hM a (max m n) (x + y)
      ((I.powerAnnihilatedSubmodule M (max m n)).add_mem hx hy),
    completionAction_eq_of_mem_stage I hM a (max m n) x hx,
    completionAction_eq_of_mem_stage I hM a (max m n) y hy]
  exact congrArg (fun z : I.powerAnnihilatedSubmodule M (max m n) ↦ (z : M))
    (smul_add (AdicCompletion.evalₐ I (max m n) a) ⟨x, hx⟩ ⟨y, hy⟩)

/-- The completed-scalar action respects the original `R`-scalar multiplication. -/
theorem completionAction_smul (I : Ideal R)
    (hM : Module.IsIdealPowerTorsion I M) (a : AdicCompletion I R) (r : R) (x : M) :
    completionAction I hM a (r • x) = r • completionAction I hM a x := by
  obtain ⟨n, hx⟩ := (Ideal.primaryComponent_mem M I x).mp (by
    rw [hM]
    exact Submodule.mem_top)
  rw [completionAction_eq_of_mem_stage I hM a n (r • x)
      ((I.powerAnnihilatedSubmodule M n).smul_mem r hx),
    completionAction_eq_of_mem_stage I hM a n x hx]
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n a)
  rw [← hs, Ideal.PowerAnnihilated.quotientAction_mk,
    Ideal.PowerAnnihilated.quotientAction_mk]
  exact smul_comm s r x

/-- A completed scalar acting as an `R`-linear endomorphism. -/
noncomputable def completionEnd (I : Ideal R)
    (hM : Module.IsIdealPowerTorsion I M) (a : AdicCompletion I R) : Module.End R M where
  toFun := completionAction I hM a
  map_add' := completionAction_add I hM a
  map_smul' := completionAction_smul I hM a

/-- Zero acts by the zero endomorphism. -/
theorem completionEnd_zero (I : Ideal R)
    (hM : Module.IsIdealPowerTorsion I M) :
    completionEnd I hM 0 = 0 := by
  ext x
  change completionAction I hM 0 x = 0
  simp [completionAction, Ideal.PowerAnnihilated.quotientAction]

/-- Addition of completed scalars acts by addition of endomorphisms. -/
theorem completionEnd_add (I : Ideal R)
    (hM : Module.IsIdealPowerTorsion I M) (a b : AdicCompletion I R) :
    completionEnd I hM (a + b) = completionEnd I hM a + completionEnd I hM b := by
  ext x
  change completionAction I hM (a + b) x =
    completionAction I hM a x + completionAction I hM b x
  simp [completionAction, Ideal.PowerAnnihilated.quotientAction, add_smul]

/-- One acts by the identity endomorphism. -/
theorem completionEnd_one (I : Ideal R)
    (hM : Module.IsIdealPowerTorsion I M) :
    completionEnd I hM 1 = 1 := by
  ext x
  change completionAction I hM 1 x = x
  simp [completionAction, Ideal.PowerAnnihilated.quotientAction]

/-- Multiplication of completed scalars acts by composition of endomorphisms. -/
theorem completionEnd_mul (I : Ideal R)
    (hM : Module.IsIdealPowerTorsion I M) (a b : AdicCompletion I R) :
    completionEnd I hM (a * b) = completionEnd I hM a * completionEnd I hM b := by
  ext x
  change completionAction I hM (a * b) x =
    completionAction I hM a (completionAction I hM b x)
  obtain ⟨n, hx⟩ := (Ideal.primaryComponent_mem M I x).mp (by
    rw [hM]
    exact Submodule.mem_top)
  rw [completionAction_eq_of_mem_stage I hM (a * b) n x hx,
    completionAction_eq_of_mem_stage I hM b n x hx]
  have hy : Ideal.PowerAnnihilated.quotientAction I n
      (AdicCompletion.evalₐ I n b) ⟨x, hx⟩ ∈ I.powerAnnihilatedSubmodule M n :=
    (AdicCompletion.evalₐ I n b • (⟨x, hx⟩ : I.powerAnnihilatedSubmodule M n)).property
  rw [completionAction_eq_of_mem_stage I hM a n _ hy]
  simpa only [map_mul, Ideal.PowerAnnihilated.quotientAction] using
    congrArg (fun z : I.powerAnnihilatedSubmodule M n ↦ (z : M))
      (mul_smul (AdicCompletion.evalₐ I n a) (AdicCompletion.evalₐ I n b)
        (⟨x, hx⟩ : I.powerAnnihilatedSubmodule M n))

/-- The canonical action of the `I`-adic completion on an `I`-power-torsion module,
as a ring homomorphism into its ring of `R`-linear endomorphisms. -/
noncomputable def completionToEnd (I : Ideal R)
    (hM : Module.IsIdealPowerTorsion I M) :
    AdicCompletion I R →+* Module.End R M where
  toFun := completionEnd I hM
  map_one' := completionEnd_one I hM
  map_mul' := completionEnd_mul I hM
  map_zero' := completionEnd_zero I hM
  map_add' := completionEnd_add I hM

/-- The completion action on an element may be evaluated at any ideal-power stage
that annihilates that element. -/
theorem completionToEnd_apply_of_mem_stage (I : Ideal R)
    (hM : Module.IsIdealPowerTorsion I M) (a : AdicCompletion I R)
    (n : ℕ) (x : M) (hx : x ∈ I.powerAnnihilatedSubmodule M n) :
    completionToEnd I hM a x =
      Ideal.PowerAnnihilated.quotientAction I n (AdicCompletion.evalₐ I n a) ⟨x, hx⟩ := by
  exact completionAction_eq_of_mem_stage I hM a n x hx

/-- The completion action extends the original scalar action along the canonical
map from `R` to its `I`-adic completion. -/
theorem completionToEnd_comp_algebraMap (I : Ideal R)
    (hM : Module.IsIdealPowerTorsion I M) :
    (completionToEnd I hM).comp (algebraMap R (AdicCompletion I R)) =
      Module.toModuleEnd R M := by
  ext r x
  change completionAction I hM (algebraMap R (AdicCompletion I R) r) x = r • x
  obtain ⟨n, hx⟩ := (Ideal.primaryComponent_mem M I x).mp (by
    rw [hM]
    exact Submodule.mem_top)
  rw [completionAction_eq_of_mem_stage I hM _ n x hx]
  have hr : AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) r) =
      Ideal.Quotient.mk (I ^ n) r := (AdicCompletion.evalₐ I n).commutes r
  rw [hr, Ideal.PowerAnnihilated.quotientAction_mk]

end Module.IsIdealPowerTorsion
