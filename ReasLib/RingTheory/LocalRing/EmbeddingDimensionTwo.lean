/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Divisibility.Units
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Data.Finite.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import ReasLib.RingTheory.CohenMacaulay.Module
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Presentation
public import ReasLib.RingTheory.LocalRing.HilbertFunction

/-!
# One-dimensional Cohen–Macaulay local rings of embedding dimension two

A cotangent linear form relatively prime to an eventual homogeneous relation
lifts to a regular element, controls maximal-ideal powers, and determines the
relation ideal and Hilbert function.
-/

@[expose] public section

universe u

open IsLocalRing MvPolynomial
open Ideal.AssociatedGraded

namespace MvPolynomial

/-- The two-variable linear form with coefficients `α` and `β` is `C α * X 0 + C β * X 1`. -/
noncomputable def linearForm {k : Type u} [CommRing k] (α β : k) : MvPolynomial (Fin 2) k :=
  C α * X 0 + C β * X 1

/-- A two-variable linear form vanishes if and only if both coefficients vanish. -/
theorem linearForm_eq_zero_iff {k : Type u} [Field k] (α β : k) :
    linearForm α β = 0 ↔ α = 0 ∧ β = 0 := by
  constructor
  · intro h
    constructor
    · simpa [linearForm] using
        congrArg (eval fun i : Fin 2 ↦ if i = 0 then (1 : k) else 0) h
    · simpa [linearForm] using
        congrArg (eval fun i : Fin 2 ↦ if i = 1 then (1 : k) else 0) h
  · rintro ⟨rfl, rfl⟩
    simp [linearForm]

/-- Every two-variable linear form is homogeneous of degree one. -/
theorem linearForm_isHomogeneous {k : Type u} [CommRing k] (α β : k) :
    (linearForm α β).IsHomogeneous 1 := by
  exact (isHomogeneous_C_mul_X α (0 : Fin 2)).add (isHomogeneous_C_mul_X β 1)

/-- Over an infinite field, every nonzero bivariate polynomial is relatively prime
to some linear form. -/
theorem exists_linearForm_isRelPrime {k : Type u} [Field k] [Infinite k]
    {F : MvPolynomial (Fin 2) k} (hF : F ≠ 0) :
    ∃ α β : k, IsRelPrime (linearForm α β) F := by
  classical
  obtain ⟨v, hv⟩ : ∃ v : Fin 2 → k, eval v (X 0 * F) ≠ 0 := by
    by_contra! h
    apply mul_ne_zero (X_ne_zero (0 : Fin 2)) hF
    apply MvPolynomial.funext
    intro v
    simpa only [map_zero] using h v
  have hv0 : v 0 ≠ 0 := by
    intro h
    exact hv (by simp [h])
  have hvF : eval v F ≠ 0 := by
    intro h
    exact hv (by simp [h])
  let L := linearForm (-(v 1)) (v 0)
  have hL : L ≠ 0 := fun h ↦ hv0 ((linearForm_eq_zero_iff _ _).mp h).2
  have hirr : Irreducible L :=
    irreducible_of_totalDegree_eq_one ((linearForm_isHomogeneous _ _).totalDegree hL)
      (by
        intro c hc
        apply isUnit_iff_ne_zero.mpr
        intro hc0
        apply hL
        ext m
        simpa only [hc0, zero_dvd_iff, coeff_zero] using hc m)
  have hnotdvd : ¬L ∣ F := by
    intro h
    have heval : eval v L = 0 := by simp [L, linearForm, mul_comm]
    apply hvF
    simpa only [heval, zero_dvd_iff] using map_dvd (eval v) h
  refine ⟨-(v 1), v 0, ?_⟩
  intro q hq hqF
  obtain ⟨r, hr⟩ := hq
  rcases hirr.isUnit_or_isUnit hr with hu | hu
  · exact hu
  · apply (hnotdvd ?_).elim
    change linearForm (-(v 1)) (v 0) ∣ F
    rw [hr]
    exact hu.mul_right_dvd.mpr hqF

end MvPolynomial

namespace IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The cotangent class of `z` is the linear combination with coefficients `α` and `β`
of the cotangent classes of the two elements in `x`. -/
def IsLinearFormClass (x : Fin 2 → maximalIdeal A) (α β : ResidueField A)
    (z : maximalIdeal A) : Prop :=
  (maximalIdeal A).toCotangent z =
    α • (maximalIdeal A).toCotangent (x 0) + β • (maximalIdeal A).toCotangent (x 1)

/-- The cotangent linear-form condition is equivalent to equality of the associated-graded
evaluation of the polynomial linear form with the degree-one class of `z`. -/
theorem isLinearFormClass_iff_degreeOne (x : Fin 2 → maximalIdeal A)
    (α β : ResidueField A) (z : maximalIdeal A) :
    IsLinearFormClass x α β z ↔
      Presentation.map x (linearForm α β) = degreeOne z := by
  let I := maximalIdeal A
  let l : I →ₗ[A] reesAlgebra I :=
    { toFun := ReesAlgebra.Grading.degreeOne I
      map_add' := fun v w ↦ by
        apply Subtype.ext
        exact (Polynomial.monomial 1).map_add v.1 w.1
      map_smul' := fun a v ↦ by
        apply Subtype.ext
        exact (Polynomial.monomial 1).map_smul a v.1 }
  let f : I →ₗ[A] ring I := (quotientMap I).toLinearMap.comp l
  have hf (v : I) : f v = degreeOne v := rfl
  have hmul (v w : I) : f (v * w) = 0 := by
    rw [hf, degreeOne, Ideal.Quotient.eq_zero_iff_mem]
    have hv : algebraMap A (reesAlgebra I) (v : A) ∈ definingIdeal I :=
      Ideal.mem_map_of_mem (algebraMap A (reesAlgebra I)) v.2
    have hprod : ReesAlgebra.Grading.degreeOne I (v * w) =
        algebraMap A (reesAlgebra I) (v : A) * ReesAlgebra.Grading.degreeOne I w := by
      apply Subtype.ext
      change Polynomial.monomial 1 ((v : A) * (w : A)) =
        Polynomial.C (v : A) * Polynomial.monomial 1 (w : A)
      rw [Polynomial.C_mul_monomial]
    rw [hprod]
    exact Ideal.mul_mem_right _ _ hv
  let g : I.Cotangent →ₗ[A] ring I := Ideal.Cotangent.lift f hmul
  have hg_apply (v : I) : g (I.toCotangent v) = degreeOne v := rfl
  -- Coefficients of degrees zero and one detect the kernel on cotangent classes.
  have hcoeff (y : reesAlgebra I) (hy : y ∈ definingIdeal I) :
      y.1.coeff 0 ∈ I ∧ y.1.coeff 1 ∈ I ^ 2 := by
    change y ∈ Submodule.span (reesAlgebra I)
      ((algebraMap A (reesAlgebra I)) '' (I : Set A)) at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      change (Polynomial.C a).coeff 0 ∈ I ∧ (Polynomial.C a).coeff 1 ∈ I ^ 2
      simpa using And.intro ha (show (0 : A) ∈ I ^ 2 from (I ^ 2).zero_mem)
    | zero => simp
    | add y w hy hw ihy ihw =>
      exact ⟨by simpa using I.add_mem ihy.1 ihw.1,
        by simpa using (I ^ 2).add_mem ihy.2 ihw.2⟩
    | smul q y hy ih =>
      change (q.1 * y.1).coeff 0 ∈ I ∧ (q.1 * y.1).coeff 1 ∈ I ^ 2
      constructor
      · rw [Polynomial.mul_coeff_zero]
        exact I.mul_mem_left _ ih.1
      · rw [Polynomial.mul_coeff_one]
        exact (I ^ 2).add_mem ((I ^ 2).mul_mem_left _ ih.2)
          (by simpa only [pow_two] using
            Ideal.mul_mem_mul (show q.1.coeff 1 ∈ I by simpa using q.2 1) ih.1)
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨v, rfl⟩ := I.toCotangent_surjective y
    apply (I.toCotangent_eq_zero v).mpr
    rw [hg_apply, degreeOne, Ideal.Quotient.eq_zero_iff_mem] at hy
    simpa only [ReesAlgebra.Grading.degreeOne, Polynomial.coeff_monomial,
      ite_true] using (hcoeff _ hy).2
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective α
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective β
  have heval : Presentation.map x
        (linearForm (Ideal.Quotient.mk I a) (Ideal.Quotient.mk I b)) =
      a • degreeOne (x 0) + b • degreeOne (x 1) := by
    simp only [I, linearForm, map_add, map_mul, Presentation.map_C, Presentation.map_X,
      quotientAlgebraMap_mk, Algebra.smul_def]
  rw [heval]
  change I.toCotangent z =
      algebraMap A (A ⧸ I) a • I.toCotangent (x 0) +
        algebraMap A (A ⧸ I) b • I.toCotangent (x 1) ↔ _
  simp only [IsScalarTower.algebraMap_smul]
  constructor
  · intro h
    simpa only [map_add, map_smul, hg_apply] using (congrArg g h).symm
  · intro h
    apply hg
    simpa only [map_add, map_smul, hg_apply] using h.symm

/-- In a one-dimensional Noetherian Cohen–Macaulay local ring of embedding dimension two,
a lift of a cotangent linear form relatively prime to the eventual homogeneous relation
is a nonzerodivisor. -/
theorem isSMulRegular_of_isLinearFormClass [IsNoetherianRing A] [Module.CohenMacaulay A A]
    (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F)
    (z : maximalIdeal A) (α β : ResidueField A) (hz : IsLinearFormClass x α β z)
    (hcoprime : IsRelPrime (linearForm α β) F) :
    IsSMulRegular A (z : A) := sorry

/-- In a one-dimensional Noetherian Cohen–Macaulay local ring of embedding dimension two,
a lift `z` of a cotangent linear form relatively prime to the eventual relation `F` satisfies
`maximalIdeal A ^ n = Ideal.span {z} ^ (n + 1 - F.totalDegree) *
maximalIdeal A ^ (F.totalDegree - 1)` for all sufficiently large `n`. -/
theorem maximalIdeal_pow_eq_span_pow_mul_pow_eventually [IsNoetherianRing A]
    [Module.CohenMacaulay A A] (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F)
    (z : maximalIdeal A) (α β : ResidueField A) (hz : IsLinearFormClass x α β z)
    (hcoprime : IsRelPrime (linearForm α β) F) :
    ∃ N ≥ F.totalDegree, ∀ n ≥ N,
      maximalIdeal A ^ n =
        Ideal.span {(z : A)} ^ (n + 1 - F.totalDegree) *
          maximalIdeal A ^ (F.totalDegree - 1) := sorry

/-- A one-dimensional Noetherian Cohen–Macaulay local ring of embedding dimension two
with infinite residue field has an element whose cotangent linear form is relatively prime
to the eventual homogeneous relation. -/
theorem exists_isLinearFormClass_isRelPrime [IsNoetherianRing A] [Module.CohenMacaulay A A]
    [Infinite (ResidueField A)] (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F) :
    ∃ (z : maximalIdeal A) (α β : ResidueField A),
      IsLinearFormClass x α β z ∧ IsRelPrime (linearForm α β) F := by
  obtain ⟨α, β, hcoprime⟩ := exists_linearForm_isRelPrime hF.1
  obtain ⟨z, hz⟩ := (maximalIdeal A).toCotangent_surjective
    (α • (maximalIdeal A).toCotangent (x 0) + β • (maximalIdeal A).toCotangent (x 1))
  exact ⟨z, α, β, hz, hcoprime⟩

/-- In a one-dimensional Noetherian Cohen–Macaulay local ring of embedding dimension two,
a lift `z` of a cotangent linear form relatively prime to the eventual relation `F` satisfies
the maximal-ideal power formula for every `n ≥ F.totalDegree`. -/
theorem maximalIdeal_pow_eq_span_pow_mul_pow [IsNoetherianRing A] [Module.CohenMacaulay A A]
    (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F)
    (z : maximalIdeal A) (α β : ResidueField A) (hz : IsLinearFormClass x α β z)
    (hcoprime : IsRelPrime (linearForm α β) F) {n : ℕ} (hn : F.totalDegree ≤ n) :
    maximalIdeal A ^ n =
      Ideal.span {(z : A)} ^ (n + 1 - F.totalDegree) *
        maximalIdeal A ^ (F.totalDegree - 1) := sorry

/-- In a one-dimensional Noetherian Cohen–Macaulay local ring of embedding dimension two,
the existence of a cotangent linear form relatively prime to the eventual homogeneous
relation implies that the associated-graded relation ideal is generated by that relation. -/
theorem associatedGradedRelIdeal_eq_span [IsNoetherianRing A] [Module.CohenMacaulay A A]
    (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F)
    (z : maximalIdeal A) (α β : ResidueField A) (hz : IsLinearFormClass x α β z)
    (hcoprime : IsRelPrime (linearForm α β) F) :
    associatedGradedRelIdeal x = Ideal.span {F} := sorry

/-- In a one-dimensional Noetherian local ring of embedding dimension two, a principal
associated-graded relation ideal generated by the eventual homogeneous relation `F` gives
Hilbert function `min (n + 1) F.totalDegree` in every positive degree `n`. -/
theorem associatedGradedHilbertFn_eq_min_succ_totalDegree_of_span [IsNoetherianRing A]
    (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F)
    (hI : associatedGradedRelIdeal x = Ideal.span {F}) {n : ℕ} (hn : 1 ≤ n) :
    associatedGradedHilbertFn A n = min (n + 1) F.totalDegree := sorry

/-- In a one-dimensional Noetherian Cohen–Macaulay local ring of embedding dimension two,
a cotangent linear form relatively prime to the eventual homogeneous relation `F` implies
that the Hilbert function in every positive degree `n` is `min (n + 1) F.totalDegree`. -/
theorem associatedGradedHilbertFn_eq_min_succ_totalDegree [IsNoetherianRing A]
    [Module.CohenMacaulay A A] (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F)
    (z : maximalIdeal A) (α β : ResidueField A) (hz : IsLinearFormClass x α β z)
    (hcoprime : IsRelPrime (linearForm α β) F) {n : ℕ} (hn : 1 ≤ n) :
    associatedGradedHilbertFn A n = min (n + 1) F.totalDegree := by
  exact associatedGradedHilbertFn_eq_min_succ_totalDegree_of_span hdim hemb x hx hF
    (associatedGradedRelIdeal_eq_span hdim hemb x hx hF z α β hz hcoprime) hn

/-- In a one-dimensional Noetherian local ring of embedding dimension two with principal
associated-graded relation ideal generated by `F`, the Hilbert function is `n + 1`
whenever `1 ≤ n < F.totalDegree`. -/
theorem associatedGradedHilbertFn_eq_succ_of_lt_totalDegree [IsNoetherianRing A]
    (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F)
    (hI : associatedGradedRelIdeal x = Ideal.span {F}) {n : ℕ} (hn : 1 ≤ n)
    (hnd : n < F.totalDegree) :
    associatedGradedHilbertFn A n = n + 1 := by
  rw [associatedGradedHilbertFn_eq_min_succ_totalDegree_of_span hdim hemb x hx hF hI hn,
    min_eq_left (Nat.succ_le_of_lt hnd)]

/-- In a one-dimensional Noetherian local ring of embedding dimension two with principal
associated-graded relation ideal generated by `F`, the Hilbert function is `F.totalDegree`
in every positive degree `n ≥ F.totalDegree`. -/
theorem associatedGradedHilbertFn_eq_totalDegree_of_ge [IsNoetherianRing A]
    (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F)
    (hI : associatedGradedRelIdeal x = Ideal.span {F}) {n : ℕ} (hn : 1 ≤ n)
    (hnd : F.totalDegree ≤ n) :
    associatedGradedHilbertFn A n = F.totalDegree := by
  rw [associatedGradedHilbertFn_eq_min_succ_totalDegree_of_span hdim hemb x hx hF hI hn,
    min_eq_right (hnd.trans (Nat.le_succ n))]

end IsLocalRing
