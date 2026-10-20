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
    evalToB π (C a) = algebraMap A B (π a) := sorry

/-- N as an A'[B]-module by restriction along `evalToB π`. -/
@[reducible] def moduleMvPolynomial (π : A' →+* A) : Module (MvPolynomial B A') N :=
  Module.compHom N (evalToB π)

/-- Evaluation of A'[B] on the opposite ring, sending rᵒᵖ to the image of r in B. -/
def evalToBOp (π : A' →+* A) : (MvPolynomial B A')ᵐᵒᵖ →+* B where
  toFun r := evalToB π (MulOpposite.unop r)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- Opposite evaluation recovers ordinary evaluation on `MulOpposite.op`. -/
theorem evalToBOp_unop (π : A' →+* A) (p : MvPolynomial B A') :
    evalToBOp π (MulOpposite.op p) = evalToB π p := sorry

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
  ⟨fun _r _n ↦ sorry⟩

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
    fstRingHom π x = TrivSqZeroExt.fst x := sorry

variable {π : A' →+* A} [π.IsSquareZeroExtension]
variable {c : KernelModule π →ₗ[A] N}
variable [IsScalarTower A B N]

/-- Coefficientwise lifts of kernel polynomials remain in the kernel of `evalToB`. -/
theorem liftPoly_mem_evalToB_ker (j : (Generators.self A B).toExtension.ker) :
    evalToB π (liftPoly π j.1) = 0 := sorry

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
    S.toB (evalPoly S j) = 0 := sorry

/-- A lifted cotangent representative evaluates into the kernel of B' → B. -/
theorem evalPoly_lift_mem_ker (S : Solution (B := B) (N := N) π c)
    (f : (Generators.self A B).toExtension.Cotangent) :
    -- Local instance justification (proof-local temporary data): bundled `S.commRing` is not globally registered on the structure Solution.
    letI := S.commRing
    S.toB (evalPoly S (liftPoly π (Function.surjInv Cotangent.mk_surjective f).1)) = 0 := sorry

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
          (evalPoly_mem_ker S hj))) := sorry

/-- The source map ψ : J' → N, sum of φ|_{J'} and δ after J' → J/J². -/
def translateKerMap (δ : (Generators.self A B).toExtension.Cotangent →ₗ[B] N)
    (S : Solution (B := B) (N := N) π c) (j : MvPolynomial B A') (hj : evalToB π j = 0) : N :=
  evalPolyKerMap S j hj + δ (Cotangent.mk ⟨map π j, sorry⟩)

/-- `translateKerMap` adds the generator-lift kernel map to the cotangent representative. -/
theorem translateKerMap_spec (δ : (Generators.self A B).toExtension.Cotangent →ₗ[B] N)
    (S : Solution (B := B) (N := N) π c) (j : MvPolynomial B A') (hj : evalToB π j = 0) :
    translateKerMap δ S j hj =
      evalPolyKerMap S j hj + δ (Cotangent.mk ⟨map π j, sorry⟩) := sorry

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
  let toB := Ideal.Quotient.lift I ((evalToB π).comp (fstRingHom π)) sorry
  -- Local instance justification (proof-local temporary data): the pushout projection is a square-zero extension by construction.
  letI : toB.IsSquareZeroExtension := ⟨sorry, sorry⟩
  Solution.of π c fromA' toB sorry
    { toFun := fun x =>
        let r := Quotient.out x.1
        TrivSqZeroExt.snd r +
          translateKerMap δ S (TrivSqZeroExt.fst r) sorry
      invFun := fun n => ofMem (x := Ideal.Quotient.mk I (TrivSqZeroExt.inr n)) sorry
      left_inv := sorry
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
      (ofMem (x := Ideal.Quotient.mk (translateGraphIdeal δ S) (TrivSqZeroExt.inr n)) sorry) = n := sorry

end SquareZeroExtension

end RingHom
