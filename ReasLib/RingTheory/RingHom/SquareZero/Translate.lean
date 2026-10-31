/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import ReasLib.RingTheory.RingHom.SquareZero.Obstruction

/-!
# Pushout translate of a square-zero solution by a naive cotangent class

Given a square-zero solution and a representative δ : J/J² →ₗ[B] N of a class
in Ext¹_B(NL_{B/A}, N), construct a second solution B'_ξ as the pushout of
A'[B] ⊕ N along ψ = φ|_{J'} + δ ∘ (J' → J/J²).
-/

@[expose] public section

noncomputable section

universe u

open MvPolynomial
open Algebra Algebra.Generators Algebra.Extension
open TrivSqZeroExt

namespace RingHom.SquareZeroExtension

variable {A' A B N : Type u} [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N] [Module A N]

/-- The canonical surjection A'[B] →+* B extending π and sending variables to themselves. -/
def evalToB (π : A' →+* A) : MvPolynomial B A' →+* B :=
  eval₂Hom ((algebraMap A B).comp π) (fun b ↦ b)

/-- Constants in A'[B] are evaluated by π followed by the structure map of B. -/
theorem evalToB_C (π : A' →+* A) (a : A') :
    evalToB π (C a) = algebraMap A B (π a) := by
  exact MvPolynomial.eval₂Hom_C _ _ _

/-- N as an A'[B]-module by restriction along `evalToB π`. -/
@[reducible] def moduleMvPolynomial (π : A' →+* A) : Module (MvPolynomial B A') N :=
  Module.compHom N (evalToB π)

/-- Evaluation of A'[B] on the opposite ring, sending rᵒᵖ to the image of r in B. -/
def evalToBOp (π : A' →+* A) : (MvPolynomial B A')ᵐᵒᵖ →+* B where
  toFun r := evalToB π (MulOpposite.unop r)
  map_one' := by simp
  map_mul' := by
    intro x y
    simp only [MulOpposite.unop_mul, map_mul]
    rw [mul_comm]
  map_zero' := by simp
  map_add' := by simp

/-- Opposite evaluation recovers ordinary evaluation on `MulOpposite.op`. -/
theorem evalToBOp_unop (π : A' →+* A) (p : MvPolynomial B A') :
    evalToBOp π (MulOpposite.op p) = evalToB π p := rfl

/-- Opposite A'[B]-action on N through the same evaluation map. -/
@[reducible] def moduleMvPolynomialOp (π : A' →+* A) : Module (MvPolynomial B A')ᵐᵒᵖ N :=
  Module.compHom N (evalToBOp π)

/-- The two A'[B]-actions on N are central. -/
theorem isCentralScalarMvPolynomial (π : A' →+* A) :
    -- Local instance justification (instance diamond): TrivSqZeroExt needs the presentation module structures keyed by π.
    letI : Module (MvPolynomial B A') N := moduleMvPolynomial π
    -- Local instance justification (instance diamond): TrivSqZeroExt needs the opposite presentation module structures keyed by π.
    letI : Module (MvPolynomial B A')ᵐᵒᵖ N := moduleMvPolynomialOp π
    IsCentralScalar (MvPolynomial B A') N :=
  -- Local instance justification (instance diamond): TrivSqZeroExt needs the presentation module structures keyed by π.
  letI : Module (MvPolynomial B A') N := moduleMvPolynomial π
  -- Local instance justification (instance diamond): TrivSqZeroExt needs the opposite presentation module structures keyed by π.
  letI : Module (MvPolynomial B A')ᵐᵒᵖ N := moduleMvPolynomialOp π
  ⟨fun r n => by
    change evalToB π (MulOpposite.unop (MulOpposite.op r)) • n =
      evalToB π r • n
    rfl⟩

/-- The canonical projection of `A'[B] ⊕ N` onto `A'[B]`. -/
def fstRingHom (π : A' →+* A) :
    -- Local instance justification (instance diamond): TrivSqZeroExt needs the presentation module structures keyed by π.
    letI : Module (MvPolynomial B A') N := moduleMvPolynomial π
    -- Local instance justification (instance diamond): TrivSqZeroExt needs the opposite presentation module structures keyed by π.
    letI : Module (MvPolynomial B A')ᵐᵒᵖ N := moduleMvPolynomialOp π
    -- Local instance justification (instance diamond): TrivSqZeroExt.commRing needs centrality of the presentation actions.
    letI : IsCentralScalar (MvPolynomial B A') N := isCentralScalarMvPolynomial π
    TrivSqZeroExt (MvPolynomial B A') N →+* MvPolynomial B A' :=
  -- Local instance justification (instance diamond): TrivSqZeroExt needs the presentation module structures keyed by π.
  letI : Module (MvPolynomial B A') N := moduleMvPolynomial π
  -- Local instance justification (instance diamond): TrivSqZeroExt needs the opposite presentation module structures keyed by π.
  letI : Module (MvPolynomial B A')ᵐᵒᵖ N := moduleMvPolynomialOp π
  -- Local instance justification (instance diamond): TrivSqZeroExt.commRing needs centrality of the presentation actions.
  letI : IsCentralScalar (MvPolynomial B A') N := isCentralScalarMvPolynomial π
  { toFun := TrivSqZeroExt.fst
    map_one' := TrivSqZeroExt.fst_one
    map_mul' := TrivSqZeroExt.fst_mul
    map_zero' := TrivSqZeroExt.fst_zero
    map_add' := TrivSqZeroExt.fst_add }

/-- `fstRingHom` acts by the first projection of the trivial square-zero extension. -/
theorem fstRingHom_apply (π : A' →+* A)
    (x :
      -- Local instance justification (instance diamond): TrivSqZeroExt needs the presentation module structures keyed by π.
      letI : Module (MvPolynomial B A') N := moduleMvPolynomial π
      -- Local instance justification (instance diamond): TrivSqZeroExt needs the opposite presentation module structures keyed by π.
      letI : Module (MvPolynomial B A')ᵐᵒᵖ N := moduleMvPolynomialOp π
      -- Local instance justification (instance diamond): TrivSqZeroExt.commRing needs centrality of the presentation actions.
      letI : IsCentralScalar (MvPolynomial B A') N := isCentralScalarMvPolynomial π
      TrivSqZeroExt (MvPolynomial B A') N) :
    -- Local instance justification (instance diamond): TrivSqZeroExt needs the presentation module structures keyed by π.
    letI : Module (MvPolynomial B A') N := moduleMvPolynomial π
    -- Local instance justification (instance diamond): TrivSqZeroExt needs the opposite presentation module structures keyed by π.
    letI : Module (MvPolynomial B A')ᵐᵒᵖ N := moduleMvPolynomialOp π
    -- Local instance justification (instance diamond): TrivSqZeroExt.commRing needs centrality of the presentation actions.
    letI : IsCentralScalar (MvPolynomial B A') N := isCentralScalarMvPolynomial π
    fstRingHom π x = TrivSqZeroExt.fst x := rfl

variable {π : A' →+* A} [π.IsSquareZeroExtension]
variable {c : KernelModule π →ₗ[A] N}
variable [IsScalarTower A B N]

/-- Coefficientwise lifts of kernel polynomials remain in the kernel of `evalToB`. -/
theorem liftPoly_mem_evalToB_ker (j : (Generators.self A B).toExtension.ker) :
    evalToB π (liftPoly π j.1) = 0 := by
  change MvPolynomial.eval₂Hom ((algebraMap A B).comp π) (fun b : B => b)
      (liftPoly π (j.1 : MvPolynomial B A)) = 0
  have hmap : MvPolynomial.map π (liftPoly π (j.1 : MvPolynomial B A)) = j.1 := by
    classical
    simp only [liftPoly, map_sum, MvPolynomial.map_monomial, Function.surjInv_eq]
    exact MvPolynomial.support_sum_monomial_coeff _
  rw [← MvPolynomial.eval₂Hom_map_hom π (fun b : B => b) (algebraMap A B)
    (liftPoly π (j.1 : MvPolynomial B A))]
  rw [hmap]
  change MvPolynomial.eval₂ (algebraMap A B) (fun b : B => b) (j.1 : MvPolynomial B A) = 0
  have hj : (algebraMap (Generators.self A B).toExtension.Ring B) j.1 = 0 :=
    (RingHom.mem_ker.mp j.property)
  change MvPolynomial.aeval (fun b : B => b) (j.1 : MvPolynomial B A) = 0 at hj
  simpa [MvPolynomial.aeval_def] using hj

/-- The A'-algebra map A'[B] → B' determined by a choice of lifts of generators. -/
def evalPoly (S : Solution (B := B) (N := N) π c) :
    -- Local instance justification (proof-local temporary data): bundled `S.commRing` is not globally registered on the structure Solution.
    letI := S.commRing
    MvPolynomial B A' →+* S.carrier :=
  -- Local instance justification (proof-local temporary data): bundled `S.commRing` is not globally registered on the structure Solution.
  letI := S.commRing
  -- Local instance justification (proof-local temporary data): bundled `S.isSquareZero` is not globally registered on the structure Solution.
  letI := S.isSquareZero
  eval₂Hom S.fromA' (Function.surjInv S.isSquareZero.surjective)

/-- Polynomials in the kernel of `evalToB π` evaluate into the kernel of B' → B. -/
theorem evalPoly_mem_ker (S : Solution (B := B) (N := N) π c) {j : MvPolynomial B A'}
    (hj : evalToB π j = 0) :
    -- Local instance justification (proof-local temporary data): bundled `S.commRing` is not globally registered on the structure Solution.
    letI := S.commRing
    S.toB (evalPoly S j) = 0 := by
  letI := S.commRing
  letI := S.isSquareZero
  calc
    S.toB (evalPoly S j) =
        MvPolynomial.eval₂Hom (S.toB.comp S.fromA')
          (fun b => S.toB (Function.surjInv S.isSquareZero.surjective b)) j := by
      exact MvPolynomial.map_eval₂Hom S.fromA'
        (Function.surjInv S.isSquareZero.surjective) S.toB j
    _ = MvPolynomial.eval₂Hom ((algebraMap A B).comp π) (fun b : B => b) j := by
      rw [S.comm_right]
      apply MvPolynomial.eval₂Hom_congr
      · rfl
      · funext b
        exact Function.rightInverse_surjInv S.isSquareZero.surjective b
      · rfl
    _ = evalToB π j := rfl
    _ = 0 := hj

/-- A lifted cotangent representative evaluates into the kernel of B' → B. -/
theorem evalPoly_lift_mem_ker (S : Solution (B := B) (N := N) π c)
    (f : (Generators.self A B).toExtension.Cotangent) :
    -- Local instance justification (proof-local temporary data): bundled `S.commRing` is not globally registered on the structure Solution.
    letI := S.commRing
    S.toB (evalPoly S (liftPoly π (Function.surjInv Cotangent.mk_surjective f).1)) = 0 := by
  apply evalPoly_mem_ker S
  exact liftPoly_mem_evalToB_ker (π := π) (Function.surjInv Cotangent.mk_surjective f)

/-- The kernel map φ_S : J' → N induced by polynomial evaluation of a solution. -/
def evalPolyKerMap (S : Solution (B := B) (N := N) π c)
    (j : MvPolynomial B A') (hj : evalToB π j = 0) : N :=
  -- Local instance justification (proof-local temporary data): bundled `S.commRing` is not globally registered on the structure Solution.
  letI := S.commRing
  -- Local instance justification (proof-local temporary data): bundled `S.isSquareZero` is not globally registered on the structure Solution.
  letI := S.isSquareZero
  S.kernelEquiv (ofMem (Iff.mpr (mem_ker (f := S.toB) (r := evalPoly S j))
      (evalPoly_mem_ker S hj)))

/-- Polynomial evaluation in the kernel of B' → B is identified with N via `kernelEquiv`. -/
theorem evalPolyKerMap_spec (S : Solution (B := B) (N := N) π c)
    (j : MvPolynomial B A') (hj : evalToB π j = 0) :
    -- Local instance justification (proof-local temporary data): bundled `S.commRing` is not globally registered on the structure Solution.
    letI := S.commRing
    -- Local instance justification (proof-local temporary data): bundled `S.isSquareZero` is not globally registered on the structure Solution.
    letI := S.isSquareZero
    evalPolyKerMap S j hj =
      S.kernelEquiv (ofMem (Iff.mpr (mem_ker (f := S.toB) (r := evalPoly S j))
          (evalPoly_mem_ker S hj))) := rfl

/-- The source map ψ : J' → N, sum of φ|_{J'} and δ after J' → J/J². -/
def translateKerMap (δ : (Generators.self A B).toExtension.Cotangent →ₗ[B] N)
    (S : Solution (B := B) (N := N) π c) (j : MvPolynomial B A') (hj : evalToB π j = 0) : N :=
  evalPolyKerMap S j hj + δ (Cotangent.mk ⟨map π j, by
    apply RingHom.mem_ker.mpr
    change MvPolynomial.aeval (fun b : B => b) (map π j) = 0
    rw [MvPolynomial.aeval_def]
    rw [MvPolynomial.eval₂_map]
    exact hj⟩)

/-- `translateKerMap` adds the generator-lift kernel map to the cotangent representative. -/
theorem translateKerMap_spec (δ : (Generators.self A B).toExtension.Cotangent →ₗ[B] N)
    (S : Solution (B := B) (N := N) π c) (j : MvPolynomial B A') (hj : evalToB π j = 0) :
    translateKerMap δ S j hj =
      evalPolyKerMap S j hj + δ (Cotangent.mk ⟨map π j, by
        apply RingHom.mem_ker.mpr
        change MvPolynomial.aeval (fun b : B => b) (map π j) = 0
        rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
        exact hj⟩) := rfl

/-- The graph ideal of ψ in the trivial square-zero extension A'[B] ⊕ N. -/
def translateGraphIdeal (δ : (Generators.self A B).toExtension.Cotangent →ₗ[B] N)
    (S : Solution (B := B) (N := N) π c) :
    -- Local instance justification (instance diamond): TrivSqZeroExt needs the presentation module structures keyed by π.
    letI : Module (MvPolynomial B A') N := moduleMvPolynomial π
    -- Local instance justification (instance diamond): TrivSqZeroExt needs the opposite presentation module structures keyed by π.
    letI : Module (MvPolynomial B A')ᵐᵒᵖ N := moduleMvPolynomialOp π
    -- Local instance justification (instance diamond): TrivSqZeroExt.commRing needs centrality of the presentation actions.
    letI : IsCentralScalar (MvPolynomial B A') N := isCentralScalarMvPolynomial π
    Ideal (TrivSqZeroExt (MvPolynomial B A') N) :=
  -- Local instance justification (instance diamond): TrivSqZeroExt needs the presentation module structures keyed by π.
  letI : Module (MvPolynomial B A') N := moduleMvPolynomial π
  -- Local instance justification (instance diamond): TrivSqZeroExt needs the opposite presentation module structures keyed by π.
  letI : Module (MvPolynomial B A')ᵐᵒᵖ N := moduleMvPolynomialOp π
  -- Local instance justification (instance diamond): TrivSqZeroExt.commRing needs centrality of the presentation actions.
  letI : IsCentralScalar (MvPolynomial B A') N := isCentralScalarMvPolynomial π
  Ideal.span <| Set.range fun j : ker (evalToB π) =>
    TrivSqZeroExt.inl j.1 - TrivSqZeroExt.inr (translateKerMap δ S j.1 (Iff.mp (mem_ker (f := evalToB π)) j.2))

/-- Pushout translation of a solution along a cotangent representative. -/
def translate (δ : (Generators.self A B).toExtension.Cotangent →ₗ[B] N)
    (S : Solution (B := B) (N := N) π c) : Solution (B := B) (N := N) π c :=
  -- Local instance justification (proof-local temporary data): bundled `S.commRing` is not globally registered on the structure Solution.
  letI := S.commRing
  -- Local instance justification (proof-local temporary data): bundled `S.isSquareZero` is not globally registered on the structure Solution.
  letI := S.isSquareZero
  -- Local instance justification (instance diamond): TrivSqZeroExt needs the presentation module structures keyed by π.
  letI : Module (MvPolynomial B A') N := moduleMvPolynomial π
  -- Local instance justification (instance diamond): TrivSqZeroExt needs the opposite presentation module structures keyed by π.
  letI : Module (MvPolynomial B A')ᵐᵒᵖ N := moduleMvPolynomialOp π
  -- Local instance justification (instance diamond): TrivSqZeroExt.commRing needs centrality of the presentation actions.
  letI : IsCentralScalar (MvPolynomial B A') N := isCentralScalarMvPolynomial π
  let I := translateGraphIdeal δ S
  let fromA' := (Ideal.Quotient.mk I).comp ((TrivSqZeroExt.inlHom (MvPolynomial B A') N).comp C)
  let toB := Ideal.Quotient.lift I ((evalToB π).comp (fstRingHom π)) (by
    intro x hx
    let hmap : TrivSqZeroExt (MvPolynomial B A') N →+* B :=
      (evalToB π).comp (fstRingHom π)
    have hI : I ≤ RingHom.ker hmap := by
      apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      apply RingHom.mem_ker.mpr
      change evalToB π (TrivSqZeroExt.fst
        (TrivSqZeroExt.inl j.1 - TrivSqZeroExt.inr
          (translateKerMap δ S j.1 (RingHom.mem_ker.mp j.2)))) = 0
      simpa only [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, sub_zero] using RingHom.mem_ker.mp j.2
    exact RingHom.mem_ker.mp (hI hx))
  have hgraph (p : MvPolynomial B A') (hp : evalToB π p = 0) :
      Ideal.Quotient.mk I (TrivSqZeroExt.inl p) =
        Ideal.Quotient.mk I (TrivSqZeroExt.inr (translateKerMap δ S p hp)) := by
    apply Ideal.Quotient.eq.mpr
    exact Ideal.subset_span ⟨⟨p, RingHom.mem_ker.mpr hp⟩, rfl⟩
  have hrepr (r : TrivSqZeroExt (MvPolynomial B A') N)
      (hr : evalToB π (TrivSqZeroExt.fst r) = 0) :
      Ideal.Quotient.mk I (TrivSqZeroExt.inr
        (TrivSqZeroExt.snd r + translateKerMap δ S (TrivSqZeroExt.fst r) hr)) =
          Ideal.Quotient.mk I r := by
    rw [TrivSqZeroExt.inr_add, map_add, ← hgraph _ hr, ← map_add]
    congr 1
    rw [add_comm]
    exact TrivSqZeroExt.inl_fst_add_inr_snd_eq r
  have hkernel (x : (TrivSqZeroExt (MvPolynomial B A') N) ⧸ I) (hx : toB x = 0) :
      ∃ n : N, Ideal.Quotient.mk I (TrivSqZeroExt.inr n) = x := by
    let r := Quotient.out x
    have hr : evalToB π (TrivSqZeroExt.fst r) = 0 := by
      have hx' := hx
      rw [← Ideal.Quotient.mk_out x] at hx'
      exact hx'
    exact ⟨_, (hrepr r hr).trans (Ideal.Quotient.mk_out x)⟩
  -- Local instance justification (proof-local temporary data): the pushout projection is a square-zero extension by construction.
  letI : toB.IsSquareZeroExtension := ⟨by
    intro b
    refine ⟨Ideal.Quotient.mk I (TrivSqZeroExt.inl (X b)), ?_⟩
    simp [toB, fstRingHom, evalToB], by
    apply le_antisymm _ bot_le
    rw [pow_two]
    apply Ideal.mul_le.mpr
    intro x hx y hy
    obtain ⟨n, hn⟩ := hkernel x (RingHom.mem_ker.mp hx)
    obtain ⟨m, hm⟩ := hkernel y (RingHom.mem_ker.mp hy)
    rw [← hn, ← hm, ← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero]
    exact (⊥ : Ideal ((TrivSqZeroExt (MvPolynomial B A') N) ⧸ I)).zero_mem⟩
  Solution.of π c fromA' toB (by
    ext a
    simp [fromA', toB, fstRingHom, evalToB, structureMap])
    { toFun := fun x =>
        let r := Quotient.out x.1
        TrivSqZeroExt.snd r +
          translateKerMap δ S (TrivSqZeroExt.fst r) (by
            have hx : toB x.1 = 0 := RingHom.mem_ker.mp x.2
            have hr : Ideal.Quotient.mk I r = x.1 := Quotient.out_eq x.1
            rw [← hr] at hx
            exact hx)
      invFun := fun n => ofMem (x := Ideal.Quotient.mk I (TrivSqZeroExt.inr n)) (by
        apply RingHom.mem_ker.mpr
        simp [toB, fstRingHom])
      left_inv := by
        intro x
        apply Subtype.ext
        have hr : evalToB π (TrivSqZeroExt.fst (Quotient.out x.1)) = 0 := by
          have hx : toB x.1 = 0 := RingHom.mem_ker.mp x.2
          rw [← Ideal.Quotient.mk_out x.1] at hx
          exact hx
        exact (hrepr (Quotient.out x.1) hr).trans (Ideal.Quotient.mk_out x.1)
      right_inv := sorry
      map_add' := sorry
      map_smul' := sorry }
    sorry

/-- The class of `inr n` in the pushout kernel is identified with `n`. -/
theorem translate_spec (δ : (Generators.self A B).toExtension.Cotangent →ₗ[B] N)
    (S : Solution (B := B) (N := N) π c) (n : N) :
    -- Local instance justification (proof-local temporary data): bundled translate carrier ring is not globally registered.
    letI := (translate δ S).commRing
    -- Local instance justification (proof-local temporary data): bundled translate square-zero instance is not globally registered.
    letI := (translate δ S).isSquareZero
    -- Local instance justification (instance diamond): TrivSqZeroExt needs the presentation module structures keyed by π.
    letI : Module (MvPolynomial B A') N := moduleMvPolynomial π
    -- Local instance justification (instance diamond): TrivSqZeroExt needs the opposite presentation module structures keyed by π.
    letI : Module (MvPolynomial B A')ᵐᵒᵖ N := moduleMvPolynomialOp π
    -- Local instance justification (instance diamond): TrivSqZeroExt.commRing needs centrality of the presentation actions.
    letI : IsCentralScalar (MvPolynomial B A') N := isCentralScalarMvPolynomial π
    (translate δ S).kernelEquiv
      (ofMem (x := Ideal.Quotient.mk (translateGraphIdeal δ S) (TrivSqZeroExt.inr n)) (by
        apply RingHom.mem_ker.mpr
        change ((evalToB π).comp (fstRingHom π)) (TrivSqZeroExt.inr n) = 0
        simp [fstRingHom, evalToB])) = n := by
  exact (translate δ S).kernelEquiv.apply_symm_apply n

end SquareZeroExtension

end RingHom
