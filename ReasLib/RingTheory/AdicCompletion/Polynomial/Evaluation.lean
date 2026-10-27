/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Over
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent
public import ReasLib.RingTheory.AdicCompletion.Polynomial

/-!
# Evaluation of adically completed polynomial rings

Evaluation at a tuple in an adically complete algebra is constructed from
compatible evaluations modulo powers of the coefficient ideal.
-/

@[expose] public section

noncomputable section

universe u

namespace Algebra.NaiveCotangent.Adic

variable {A ι : Type u} [CommRing A]

/-- The image of the indeterminate `MvPolynomial.X i` in `A[x_ι]^∧`. -/
def X (I : Ideal A) (i : ι) : polynomialCompletion A I ι :=
  AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) (MvPolynomial.X i)

variable {C : Type u} [CommRing C] [Algebra A C]

/-- Polynomial evaluation sends the extended coefficient ideal into its extension. -/
theorem aeval_ideal_le (I : Ideal A) (v : ι → C) :
    polynomialIdeal A I ι ≤
      Ideal.comap (MvPolynomial.aeval v) (I.map (algebraMap A C)) := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro a ha
  change (MvPolynomial.aeval v) (algebraMap A (MvPolynomial ι A) a) ∈
    I.map (algebraMap A C)
  simpa using Ideal.mem_map_of_mem (algebraMap A C) ha

/-- Finite-stage evaluation of an element of `A[x_ι]^∧` at a tuple `v`, landing in
`C ⧸ (I.map (algebraMap A C)) ^ n`. -/
def adicAevalStage (I : Ideal A) (v : ι → C) (n : ℕ) :
    polynomialCompletion A I ι →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n :=
  (Ideal.quotientMapₐ ((I.map (algebraMap A C)) ^ n) (MvPolynomial.aeval v)
      ((Ideal.pow_right_mono (aeval_ideal_le I v) n).trans
        (Ideal.le_comap_pow (MvPolynomial.aeval v).toRingHom n))).comp
    ((AdicCompletion.evalₐ (polynomialIdeal A I ι) n).restrictScalars A)

/-- Polynomial evaluation at a finite stage agrees with ordinary polynomial evaluation. -/
private theorem adicAevalStage_of (I : Ideal A) (v : ι → C) (n : ℕ)
    (p : MvPolynomial ι A) :
    adicAevalStage I v n
        (AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) p) =
      Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ n) (MvPolynomial.aeval v p) := by
  simp [adicAevalStage, AdicCompletion.evalₐ_of]

/-- Finite-stage evaluation sends the indeterminate `X I i` to the residue of `v i`. -/
theorem adicAevalStage_X (I : Ideal A) (v : ι → C) (n : ℕ) (i : ι) :
    adicAevalStage I v n (X I i) =
      Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ n) (v i) := by
  simpa [X] using adicAevalStage_of I v n (MvPolynomial.X i)

/-- The polynomial completion projections commute with quotient transition maps. -/
private theorem factor_polynomialEval (I : Ideal A) {m n : ℕ} (hle : m ≤ n)
    (x : polynomialCompletion A I ι) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hle)
        (AdicCompletion.evalₐ (polynomialIdeal A I ι) n x) =
      AdicCompletion.evalₐ (polynomialIdeal A I ι) m x := by
  rw [← AdicCompletion.factor_eval_eq_evalₐ (polynomialIdeal A I ι) x (by simp),
    ← AdicCompletion.factor_eval_eq_evalₐ (polynomialIdeal A I ι) x (by simp)]
  change _ = Ideal.Quotient.factor
    (show (polynomialIdeal A I ι) ^ m • (⊤ : Ideal (MvPolynomial ι A)) ≤
      (polynomialIdeal A I ι) ^ m by simp) (x.val m)
  rw [← x.property hle]
  obtain ⟨p, hp⟩ := Submodule.mkQ_surjective
    ((polynomialIdeal A I ι) ^ n • ⊤ : Submodule (MvPolynomial ι A) (MvPolynomial ι A))
    (x.val n)
  simp only [AdicCompletion.eval_apply]
  rw [← hp]
  rfl

/-- Finite-stage evaluations are compatible with the inverse system of quotients
`C ⧸ (I C) ^ n`. -/
theorem adicAevalStage_compatible (I : Ideal A) (v : ι → C) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hle)).comp (adicAevalStage I v n) =
      adicAevalStage I v m := by
  ext x
  simp only [adicAevalStage, AlgHom.comp_apply, AlgHom.restrictScalars_apply]
  rw [← factor_polynomialEval I hle x]
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (polynomialIdeal A I ι) n x)
  rw [← hp]
  rfl

/-- The `A`-algebra map `A[x_ι]^∧ →ₐ[A] C` evaluating the variables at `v`,
obtained from the inverse-limit universal property of an `I`-adically complete algebra.
Uniqueness among all such maps holds under finite generation of `I`; see `eq_adicAeval`. -/
def adicAeval (I : Ideal A) [IsAdicComplete (I.map (algebraMap A C)) C] (v : ι → C) :
    polynomialCompletion A I ι →ₐ[A] C :=
  IsAdicComplete.liftAlgHom (I.map (algebraMap A C)) (fun n ↦ adicAevalStage I v n)
    (adicAevalStage_compatible I v)

/-- Completed evaluation sends the indeterminate `X I i` to `v i`. -/
theorem adicAeval_X (I : Ideal A) [IsAdicComplete (I.map (algebraMap A C)) C] (v : ι → C)
    (i : ι) : adicAeval I v (X I i) = v i :=
  congrFun (IsHausdorff.funext' (I.map (algebraMap A C))
    (f := fun _ : Unit ↦ adicAeval I v (X I i)) (g := fun _ ↦ v i)
    (fun n _ ↦ by simp [adicAeval, IsAdicComplete.mk_liftAlgHom, adicAevalStage_X])) ()

/-- Completed evaluation extends ordinary polynomial evaluation along the dense map
from `A[x_ι]`. -/
theorem adicAeval_comp_of (I : Ideal A) [IsAdicComplete (I.map (algebraMap A C)) C] (v : ι → C)
    (p : MvPolynomial ι A) :
    adicAeval I v (AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) p) =
      MvPolynomial.aeval v p :=
  congrFun (IsHausdorff.funext' (I.map (algebraMap A C))
    (f := fun _ : Unit ↦ adicAeval I v
      (AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) p))
    (g := fun _ ↦ MvPolynomial.aeval v p)
    (fun n _ ↦ by simp [adicAeval, IsAdicComplete.mk_liftAlgHom, adicAevalStage_of])) ()

/-- Every completed polynomial has a polynomial representative modulo each power
of the coefficient ideal, when that ideal is finitely generated. -/
private theorem exists_polynomial_mod_pow (I : Ideal A) (hI : I.FG) (n : ℕ)
    (x : polynomialCompletion A I ι) :
    ∃ p : MvPolynomial ι A,
      x - AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) p ∈
        (I ^ n • ⊤ : Submodule A (polynomialCompletion A I ι)) := by
  obtain ⟨p, hp⟩ := Submodule.mkQ_surjective
    ((polynomialIdeal A I ι) ^ n • ⊤ : Submodule (MvPolynomial ι A) (MvPolynomial ι A))
    (AdicCompletion.eval (polynomialIdeal A I ι) (MvPolynomial ι A) n x)
  have hx : x - AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) p ∈
      ((polynomialIdeal A I ι) ^ n • ⊤ :
        Submodule (MvPolynomial ι A) (polynomialCompletion A I ι)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval
      (I := polynomialIdeal A I ι) (M := MvPolynomial ι A) (n := n)
      (Ideal.FG.map hI (algebraMap A (MvPolynomial ι A))),
      LinearMap.mem_ker, map_sub, AdicCompletion.eval_of, sub_eq_zero]
    exact hp.symm
  change x - AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) p ∈
    ((((I.map (algebraMap A (MvPolynomial ι A))) ^ n) • ⊤ :
      Submodule (MvPolynomial ι A) (polynomialCompletion A I ι)).restrictScalars A) at hx
  rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top] at hx
  exact ⟨p, hx⟩

/-- An algebra map preserves each coefficient-ideal filtration step. -/
private theorem algHom_maps_pow (I : Ideal A) (ψ : polynomialCompletion A I ι →ₐ[A] C)
    (n : ℕ) {x : polynomialCompletion A I ι}
    (hx : x ∈ (I ^ n • ⊤ : Submodule A (polynomialCompletion A I ι))) :
    ψ x ∈ (I.map (algebraMap A C)) ^ n := by
  have hm : Submodule.map ψ.toLinearMap (I ^ n • ⊤) ≤
      (I ^ n • ⊤ : Submodule A C) := by
    rw [Submodule.map_smul'']
    exact smul_mono_right _ le_top
  have hψ := (Submodule.map_le_iff_le_comap.mp hm) hx
  simpa [Ideal.smul_top_eq_map, Ideal.map_pow] using hψ

/-- An `A`-algebra map out of `A[x_ι]^∧` is determined by its indeterminates when
`I` is finitely generated and the target is adically complete. -/
theorem eq_adicAeval {I : Ideal A} (hI : I.FG)
    [IsAdicComplete (I.map (algebraMap A C)) C]
    (ψ : polynomialCompletion A I ι →ₐ[A] C) :
    ψ = adicAeval I fun i ↦ ψ (X I i) := by
  let f := adicAeval I fun i ↦ ψ (X I i)
  have hpoly (p : MvPolynomial ι A) :
      ψ (AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) p) =
        MvPolynomial.aeval (fun i ↦ ψ (X I i)) p := by
    exact AlgHom.congr_fun (MvPolynomial.aeval_unique
      (ψ.comp (IsScalarTower.toAlgHom A (MvPolynomial ι A) (polynomialCompletion A I ι)))) p
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' (I.map (algebraMap A C))
  intro n x
  obtain ⟨p, hp⟩ := exists_polynomial_mod_pow I hI n x
  have hψ : ψ x - ψ (AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) p) ∈
      (I.map (algebraMap A C)) ^ n := by
    rw [← map_sub]
    exact algHom_maps_pow I ψ n hp
  have hf : f x - f (AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) p) ∈
      (I.map (algebraMap A C)) ^ n := by
    rw [← map_sub]
    exact algHom_maps_pow I f n hp
  have heq : ψ (AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) p) =
      f (AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) p) := by
    rw [hpoly, adicAeval_comp_of]
  calc
    Ideal.Quotient.mk _ (ψ x) =
        Ideal.Quotient.mk _ (ψ (AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) p)) :=
      Ideal.Quotient.eq.mpr hψ
    _ = Ideal.Quotient.mk _ (f (AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) p)) :=
      congrArg (Ideal.Quotient.mk _) heq
    _ = Ideal.Quotient.mk _ (f x) := (Ideal.Quotient.eq.mpr hf).symm

/-- The perturbation of `ψ` sending `X I i` to `ψ (X I i) + δ i`. -/
def aevalShift {I : Ideal A} [IsAdicComplete (I.map (algebraMap A C)) C]
    (ψ : polynomialCompletion A I ι →ₐ[A] C) (δ : ι → C) :
    polynomialCompletion A I ι →ₐ[A] C :=
  adicAeval I fun i ↦ ψ (X I i) + δ i

/-- The shifted map sends the indeterminate `X I i` to `ψ (X I i) + δ i`. -/
theorem aevalShift_X {I : Ideal A} [IsAdicComplete (I.map (algebraMap A C)) C]
    (ψ : polynomialCompletion A I ι →ₐ[A] C) (δ : ι → C) (i : ι) :
    aevalShift ψ δ (X I i) = ψ (X I i) + δ i := by
  exact adicAeval_X I _ i

end Algebra.NaiveCotangent.Adic
