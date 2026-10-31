/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Presentation
public import ReasLib.RingTheory.MvPolynomial.EventualPrincipal

/-!
# Hilbert functions of one-dimensional local rings

This file owns the residue-field Hilbert function, the relation ideal of a
two-generator associated-graded presentation, and the embedding-dimension-two
consequences for that Hilbert function.
-/

@[expose] public section

noncomputable section

universe u

open Filter MvPolynomial

namespace IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The residue-field Hilbert function sends a degree to the finrank of the
corresponding maximal-ideal associated-graded piece. -/
def associatedGradedHilbertFn (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) : ℕ :=
  Module.finrank (ResidueField A) (Ideal.AssociatedGraded.piece (maximalIdeal A) A n)

/-- The degree-zero value of the residue-field Hilbert function is one. -/
theorem associatedGradedHilbertFn_zero (A : Type u) [CommRing A] [IsLocalRing A] :
    associatedGradedHilbertFn A 0 = 1 := by
  let I := maximalIdeal A
  have hzero : Ideal.AssociatedGraded.stage I A 0 = ⊤ := by
    simpa using Ideal.PowerSubmodule.stage_regular I 0
  have hone : Ideal.AssociatedGraded.stage I A (0 + 1) = I := by
    simpa using Ideal.PowerSubmodule.stage_regular I 1
  let e := LinearEquiv.ofTop (Ideal.AssociatedGraded.stage I A 0) hzero
  have hmap : (Ideal.AssociatedGraded.denominator I A 0).map e.toLinearMap = I := by
    ext a
    constructor
    · rintro ⟨y, hy, rfl⟩
      change (y : A) ∈ I
      change (y : A) ∈ Ideal.AssociatedGraded.stage I A (0 + 1) at hy
      rwa [hone] at hy
    · intro ha
      refine ⟨e.symm a, ?_, e.apply_symm_apply a⟩
      change a ∈ Ideal.AssociatedGraded.stage I A (0 + 1)
      rwa [hone]
  letI : IsScalarTower A (A ⧸ maximalIdeal A)
      (Ideal.AssociatedGraded.piece (maximalIdeal A) A 0) :=
    Ideal.AssociatedGraded.pieceIsScalarTowerQuotient _ _ _
  let e' : Ideal.AssociatedGraded.piece (maximalIdeal A) A 0 ≃ₗ[A ⧸ maximalIdeal A]
      A ⧸ maximalIdeal A := (Submodule.Quotient.equiv _ _ e hmap).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective
  exact e'.finrank_eq.trans (CommSemiring.finrank_self (A ⧸ maximalIdeal A))

/-- Every maximal-ideal associated-graded piece of a Noetherian local ring is
finite-dimensional over its residue field. -/
instance finiteDimensional_associatedGradedPiece [IsNoetherianRing A] (n : ℕ) :
    FiniteDimensional (ResidueField A)
      (Ideal.AssociatedGraded.piece (maximalIdeal A) A n) := by
  letI : IsScalarTower A (ResidueField A)
      (Ideal.AssociatedGraded.piece (maximalIdeal A) A n) :=
    Ideal.AssociatedGraded.pieceIsScalarTowerQuotient _ _ _
  exact Module.Finite.of_restrictScalars_finite A _ _

/-- The relation ideal is the kernel of the polynomial presentation map
determined by a two-element family in the maximal ideal. -/
def associatedGradedRelIdeal (x : Fin 2 → maximalIdeal A) :
    Ideal (MvPolynomial (Fin 2) (ResidueField A)) :=
  RingHom.ker (Ideal.AssociatedGraded.Presentation.map x)

/-- Membership in the relation ideal is equivalent to vanishing under the
associated-graded polynomial presentation map. -/
theorem mem_associatedGradedRelIdeal (x : Fin 2 → maximalIdeal A)
    (p : MvPolynomial (Fin 2) (ResidueField A)) :
    p ∈ associatedGradedRelIdeal x ↔
      Ideal.AssociatedGraded.Presentation.map x p = 0 := Iff.rfl

private theorem presentation_map_mem_grade {R : Type*} [CommRing R] {ι : Type*}
    {I : Ideal R} (x : ι → I) {q : MvPolynomial ι (R ⧸ I)} {d : ℕ}
    (hq : q.IsHomogeneous d) :
    Ideal.AssociatedGraded.Presentation.map x q ∈ Ideal.AssociatedGraded.grade I d := by
  classical
  induction hq using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
    simpa only [map_zero] using (Submodule.zero_mem (Ideal.AssociatedGraded.grade I d))
  | add q r _ _ hq hr =>
    simpa only [map_add] using Submodule.add_mem _ hq hr
  | monomial a r ha =>
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [Ideal.AssociatedGraded.Presentation.map, MvPolynomial.aeval_monomial,
      Ideal.AssociatedGraded.quotientAlgebraMap_mk]
    have hc : algebraMap R (Ideal.AssociatedGraded.ring I) s ∈
        Ideal.AssociatedGraded.grade I 0 := by
      simpa only [Algebra.algebraMap_eq_smul_one] using
        (Ideal.AssociatedGraded.grade I 0).smul_mem s (SetLike.one_mem_graded _)
    have ha' : a.degree = d := by
      change (Finsupp.weight (fun _ : ι ↦ 1)) a = d at ha
      simpa only [Finsupp.degree_eq_weight_one] using ha
    have hprod : a.prod (fun i e ↦ Ideal.AssociatedGraded.degreeOne (x i) ^ e) ∈
        Ideal.AssociatedGraded.grade I d := by
      simpa only [Finsupp.prod, nsmul_eq_mul, Nat.cast_id, mul_one,
        ← Finsupp.degree_apply, ha'] using
        SetLike.prod_pow_mem_graded (Ideal.AssociatedGraded.grade I)
          (fun _ : ι ↦ 1) (fun i ↦ Ideal.AssociatedGraded.degreeOne (x i))
          (F := a.support) a (fun i _ ↦ Ideal.AssociatedGraded.degreeOne_mem_grade (x i))
    simpa only [zero_add] using SetLike.mul_mem_graded hc hprod

/-- The relation ideal is closed under taking homogeneous components. -/
theorem associatedGradedRelIdeal_isHomogeneous (x : Fin 2 → maximalIdeal A)
    (p : MvPolynomial (Fin 2) (ResidueField A)) (n : ℕ) :
    p ∈ associatedGradedRelIdeal x →
      homogeneousComponent n p ∈ associatedGradedRelIdeal x := by
  classical
  letI := MvPolynomial.gradedAlgebra (σ := Fin 2) (R := A ⧸ maximalIdeal A)
  let f : homogeneousSubmodule (Fin 2) (A ⧸ maximalIdeal A) →+*ᵍ
      Ideal.AssociatedGraded.grade (maximalIdeal A) :=
    { (Ideal.AssociatedGraded.Presentation.map x).toRingHom with
      map_mem := presentation_map_mem_grade x }
  have hkernel (q : MvPolynomial (Fin 2) (A ⧸ maximalIdeal A))
      (hq : Ideal.AssociatedGraded.Presentation.map x q = 0) :
      Ideal.AssociatedGraded.Presentation.map x (homogeneousComponent n q) = 0 := by
    have hcomponent :
        (DirectSum.decompose (homogeneousSubmodule (Fin 2) (A ⧸ maximalIdeal A)) q n :
          MvPolynomial (Fin 2) (A ⧸ maximalIdeal A)) = homogeneousComponent n q :=
      MvPolynomial.decomposition.decompose'_apply q n
    calc
      Ideal.AssociatedGraded.Presentation.map x (homogeneousComponent n q) =
          Ideal.AssociatedGraded.Presentation.map x
            (DirectSum.decompose (homogeneousSubmodule (Fin 2) (A ⧸ maximalIdeal A)) q n) :=
        congrArg (Ideal.AssociatedGraded.Presentation.map x) hcomponent.symm
      _ = (DirectSum.decompose (Ideal.AssociatedGraded.grade (maximalIdeal A))
          (Ideal.AssociatedGraded.Presentation.map x q) n :
            Ideal.AssociatedGraded.ring (maximalIdeal A)) :=
        f.map_directSumDecompose (x := q) (i := n)
      _ = 0 := by simp [hq]
  exact hkernel p

/-- A one-dimensional Noetherian local ring with two-dimensional cotangent
space has an eventually homogeneous principal relation ideal. -/
theorem exists_homogeneousEventuallySpan (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A) :
    ∃ F, IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F := sorry

/-- Under the same hypotheses, the residue-field Hilbert function is bounded
above by the dimension of the degree-`n` piece of a two-variable polynomial
ring. -/
theorem associatedGradedHilbertFn_le_succ (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2) (n : ℕ) :
    associatedGradedHilbertFn A n ≤ n + 1 := sorry

/-- If the Hilbert function has a strict deficit in degree `n`, the total degree
of an eventual homogeneous generator is at most `n`. -/
theorem associatedGradedHilbertFn_lt_succ_imp_totalDegree_le (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F) {n : ℕ}
    (hn : associatedGradedHilbertFn A n < n + 1) :
    F.totalDegree ≤ n := sorry

/-- A strict deficit in degree `n` makes the next Hilbert value no larger than
the value in degree `n`. -/
theorem associatedGradedHilbertFn_lt_succ_antitone (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2) {n : ℕ}
    (hn : associatedGradedHilbertFn A n < n + 1) :
    associatedGradedHilbertFn A (n + 1) ≤ associatedGradedHilbertFn A n := sorry

/-- The residue-field Hilbert function eventually equals the total degree of an
eventual homogeneous generator of the relation ideal. -/
theorem associatedGradedHilbertFn_eventually_eq_totalDegree (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F) :
    ∀ᶠ n in atTop, associatedGradedHilbertFn A n = F.totalDegree := sorry

end IsLocalRing
