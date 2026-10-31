/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Extension.Generators
public import ReasLib.RingTheory.Extension.Cotangent.ExtOne
public import ReasLib.RingTheory.RingHom.SquareZero.Diagram

/-!
# Canonical obstruction of a relative square-zero diagram

The obstruction is the quotient class obtained by comparing polynomial
evaluations of chosen generator lifts.
-/

@[expose] public section

noncomputable section

universe u

open RingHom
open MvPolynomial
open Algebra Algebra.Generators Algebra.Extension
open RingHom.SquareZeroExtension

namespace RingHom.SquareZeroExtension


variable {A₁' A₁ B₁ N₁ : Type u} {A₂' A₂ B₂ N₂ : Type u}
variable [CommRing A₁'] [CommRing A₁] [CommRing B₁] [Algebra A₁ B₁]
variable [CommRing A₂'] [CommRing A₂] [CommRing B₂] [Algebra A₂ B₂]
variable [AddCommGroup N₁] [Module B₁ N₁] [Module A₁ N₁] [IsScalarTower A₁ B₁ N₁]
variable [AddCommGroup N₂] [Module B₂ N₂] [Module A₂ N₂] [IsScalarTower A₂ B₂ N₂]
variable {π₁ : A₁' →+* A₁} [π₁.IsSquareZeroExtension]
variable {π₂ : A₂' →+* A₂} [π₂.IsSquareZeroExtension]
variable {c₁ : KernelModule π₁ →ₗ[A₁] N₁}
variable {c₂ : KernelModule π₂ →ₗ[A₂] N₂}
variable {S₁ : Solution (B := B₁) (N := N₁) π₁ c₁} {S₂ : Solution (B := B₂) (N := N₂) π₂ c₂}

/-- Coefficientwise lift of a polynomial along a set-theoretic section of a square-zero
surjection. -/
def liftPoly (π : A₁' →+* A₁) [hπ : π.IsSquareZeroExtension] :
    MvPolynomial B₁ A₁ → MvPolynomial B₁ A₁' :=
  fun p ↦ p.support.sum fun d ↦ monomial d (Function.surjInv hπ.surjective (p.coeff d))

/-- `liftPoly` changes coefficients along a section of π. -/
theorem liftPoly_coeff (π : A₁' →+* A₁) [hπ : π.IsSquareZeroExtension]
    (p : MvPolynomial B₁ A₁) (d : B₁ →₀ ℕ) :
    (d ∈ p.support →
      (liftPoly π p).coeff d = Function.surjInv hπ.surjective (p.coeff d)) ∧
      (d ∉ p.support → (liftPoly π p).coeff d = 0) := by
  classical
  constructor
  · intro hd
    simp [liftPoly, coeff_sum, coeff_monomial, hd]
  · intro hd
    simp [liftPoly, coeff_sum, coeff_monomial, hd]

/-- The coefficientwise section projects back to the original polynomial. -/
theorem liftPoly_map (π : A₁' →+* A₁) [hπ : π.IsSquareZeroExtension]
    (p : MvPolynomial B₁ A₁) :
    MvPolynomial.map π (liftPoly π p) = p := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [coeff_map]
  by_cases hd : d ∈ p.support
  · rw [(liftPoly_coeff π p d).1 hd]
    exact Function.rightInverse_surjInv hπ.surjective _
  · rw [(liftPoly_coeff π p d).2 hd, map_zero]
    exact (notMem_support_iff.mp hd).symm

namespace RelativeDiagram

/-- A set-theoretic section of the front projection B'₁ → B₁. -/
def generatorLiftFront :
    -- Local instance justification (proof-local temporary data): bundled `S₁.commRing` is not globally registered on the structure Solution.
    letI := S₁.commRing
    B₁ → S₁.carrier :=
  -- Local instance justification (proof-local temporary data): bundled `S₁.commRing` is not globally registered on the structure Solution.
  letI := S₁.commRing
  -- Local instance justification (proof-local temporary data): bundled `S₁.isSquareZero` is not globally registered on the structure Solution.
  letI := S₁.isSquareZero
  Function.surjInv S₁.isSquareZero.surjective

/-- The chosen front generator lift projects to the original generator. -/
theorem generatorLiftFront_spec (b : B₁) :
    S₁.toB (generatorLiftFront b) = b := by
  letI := S₁.commRing
  letI := S₁.isSquareZero
  change S₁.toB (Function.surjInv S₁.isSquareZero.surjective b) = b
  exact Function.rightInverse_surjInv S₁.isSquareZero.surjective b

/-- A set-theoretic lift of g along the back projection B'₂ → B₂. -/
def generatorLiftBack (D : RelativeDiagram S₁ S₂) :
    -- Local instance justification (proof-local temporary data): bundled `S₂.commRing` is not globally registered on the structure Solution.
    letI := S₂.commRing
    B₁ → S₂.carrier :=
  -- Local instance justification (proof-local temporary data): bundled `S₂.commRing` is not globally registered on the structure Solution.
  letI := S₂.commRing
  -- Local instance justification (proof-local temporary data): bundled `S₂.isSquareZero` is not globally registered on the structure Solution.
  letI := S₂.isSquareZero
  fun e ↦ Function.surjInv S₂.isSquareZero.surjective (D.g e)

/-- The chosen back generator lift projects to its connecting image. -/
theorem generatorLiftBack_spec (D : RelativeDiagram S₁ S₂) (b : B₁) :
    S₂.toB (generatorLiftBack D b) = D.g b := by
  letI := S₂.commRing
  letI := S₂.isSquareZero
  change S₂.toB (Function.surjInv S₂.isSquareZero.surjective (D.g b)) = D.g b
  exact Function.rightInverse_surjInv S₂.isSquareZero.surjective (D.g b)

/-- The A'₁-algebra map A'₁[B₁] → B'₁ determined by front generator lifts. -/
def evalFront :
    -- Local instance justification (proof-local temporary data): bundled `S₁.commRing` is not globally registered on the structure Solution.
    letI := S₁.commRing
    MvPolynomial B₁ A₁' →+* S₁.carrier :=
  -- Local instance justification (proof-local temporary data): bundled `S₁.commRing` is not globally registered on the structure Solution.
  letI := S₁.commRing
  eval₂Hom S₁.fromA' generatorLiftFront

/-- The A'₁-algebra map A'₁[B₁] → B'₂ determined by back generator lifts. -/
def evalBack (D : RelativeDiagram S₁ S₂) :
    -- Local instance justification (proof-local temporary data): bundled `S₂.commRing` is not globally registered on the structure Solution.
    letI := S₂.commRing
    MvPolynomial B₁ A₁' →+* S₂.carrier :=
  -- Local instance justification (proof-local temporary data): bundled `S₂.commRing` is not globally registered on the structure Solution.
  letI := S₂.commRing
  eval₂Hom (S₂.fromA'.comp D.t') (generatorLiftBack D)

/-- Front evaluation of a lifted cotangent representative lands in ker(B'₁ → B₁). -/
theorem evalFront_lift_mem_ker (D : RelativeDiagram S₁ S₂)
    (f : (Generators.self A₁ B₁).toExtension.Cotangent) :
    -- Local instance justification (proof-local temporary data): bundled `S₁.commRing` is not globally registered on the structure Solution.
    letI := S₁.commRing
    S₁.toB (evalFront (liftPoly π₁
      (Function.surjInv Cotangent.mk_surjective f).1)) = 0 := by
  letI := S₁.commRing
  letI := S₁.isSquareZero
  let x := Function.surjInv Cotangent.mk_surjective f
  let p' := liftPoly π₁ x.1
  have hx : MvPolynomial.aeval (R := A₁) (Generators.self A₁ B₁).val x.1 = 0 :=
    Generators.aeval_val_eq_zero x.2
  change S₁.toB (MvPolynomial.eval₂Hom S₁.fromA' generatorLiftFront p') = 0
  rw [MvPolynomial.map_eval₂Hom]
  simp_rw [generatorLiftFront_spec]
  rw [S₁.comm_right]
  change MvPolynomial.eval₂Hom ((algebraMap A₁ B₁).comp π₁)
    (fun b : B₁ => b) p' = 0
  rw [← MvPolynomial.eval₂Hom_map_hom π₁ (fun b : B₁ => b)
    (algebraMap A₁ B₁) p']
  rw [liftPoly_map]
  have hid : (fun b : B₁ => b) = (_root_.id : B₁ → B₁) := rfl
  rw [hid]
  simpa [MvPolynomial.aeval_def, Generators.self, id] using hx

/-- Back evaluation of a lifted cotangent representative lands in ker(B'₂ → B₂). -/
theorem evalBack_lift_mem_ker (D : RelativeDiagram S₁ S₂)
    (f : (Generators.self A₁ B₁).toExtension.Cotangent) :
    -- Local instance justification (proof-local temporary data): bundled `S₂.commRing` is not globally registered on the structure Solution.
    letI := S₂.commRing
    S₂.toB (evalBack D (liftPoly π₁
      (Function.surjInv Cotangent.mk_surjective f).1)) = 0 := by
  letI := S₂.commRing
  letI := S₂.isSquareZero
  let x := Function.surjInv Cotangent.mk_surjective f
  let p' := liftPoly π₁ x.1
  have hx : MvPolynomial.aeval (R := A₁) (Generators.self A₁ B₁).val x.1 = 0 :=
    Generators.aeval_val_eq_zero x.2
  change S₂.toB (MvPolynomial.eval₂Hom (S₂.fromA'.comp D.t')
    (generatorLiftBack D) p') = 0
  rw [MvPolynomial.map_eval₂Hom]
  simp_rw [generatorLiftBack_spec]
  rw [← RingHom.comp_assoc, S₂.comm_right]
  rw [RingHom.comp_assoc, D.comm_base]
  change MvPolynomial.eval₂Hom
    (((algebraMap A₂ B₂).comp D.t).comp π₁) (D.g) p' = 0
  rw [← D.comm_alg]
  rw [← MvPolynomial.eval₂Hom_map_hom π₁ (D.g : B₁ → B₂)
    (D.g.comp (algebraMap A₁ B₁)) p']
  rw [liftPoly_map]
  rw [← MvPolynomial.map_eval₂Hom (algebraMap A₁ B₁) (fun b : B₁ => b)
    D.g x.1]
  have hid : (fun b : B₁ => b) = (_root_.id : B₁ → B₁) := rfl
  rw [hid]
  simpa [MvPolynomial.aeval_def, Generators.self, id] using congrArg D.g hx

/-- The restricted Hom space of conormal representatives. -/
abbrev ConormalMaps (D : RelativeDiagram S₁ S₂) : Type u :=
  -- Local instance justification (noncanonical choice): conormal coefficients use N₂ restricted along D.g.
  letI := moduleRestrict D
  (Generators.self A₁ B₁).toExtension.Cotangent →ₗ[B₁] N₂

/-- The obstruction representative Hom_B₁(J/J², N₂) obtained by comparing generator lifts. -/
def conormalHom (D : RelativeDiagram S₁ S₂) : ConormalMaps D :=
  -- Local instance justification (noncanonical choice): the B₁-action on N₂ is restriction along D.g.
  letI := moduleRestrict D
  { toFun := fun f ↦
    -- Local instance justification (proof-local temporary data): bundled `S₁.commRing` is not globally registered on the structure Solution.
    letI := S₁.commRing
    -- Local instance justification (proof-local temporary data): bundled `S₂.commRing` is not globally registered on the structure Solution.
    letI := S₂.commRing
    -- Local instance justification (proof-local temporary data): bundled `S₁.isSquareZero` is not globally registered on the structure Solution.
    letI := S₁.isSquareZero
    -- Local instance justification (proof-local temporary data): bundled `S₂.isSquareZero` is not globally registered on the structure Solution.
    letI := S₂.isSquareZero
    let x := Function.surjInv Cotangent.mk_surjective f
    let f' := liftPoly π₁ x.1
    S₂.kernelEquiv (ofMem (Iff.mpr (mem_ker (f := S₂.toB) (r := evalBack D f'))
        (evalBack_lift_mem_ker D f))) -
      D.ν (S₁.kernelEquiv (ofMem (Iff.mpr (mem_ker (f := S₁.toB) (r := evalFront f'))
        (evalFront_lift_mem_ker D f)))),
    map_add' := sorry
    map_smul' := sorry }

/-- `conormalHom` compares the back and front evaluations of a lifted cotangent class. -/
theorem conormalHom_apply (D : RelativeDiagram S₁ S₂)
    (f : (Generators.self A₁ B₁).toExtension.Cotangent) :
    -- Local instance justification (noncanonical choice): the B₁-action on N₂ is restriction along D.g.
    letI := moduleRestrict D
    conormalHom D f =
      -- Local instance justification (proof-local temporary data): bundled `S₁.commRing` is not globally registered on the structure Solution.
      letI := S₁.commRing
      -- Local instance justification (proof-local temporary data): bundled `S₂.commRing` is not globally registered on the structure Solution.
      letI := S₂.commRing
      -- Local instance justification (proof-local temporary data): bundled `S₁.isSquareZero` is not globally registered on the structure Solution.
      letI := S₁.isSquareZero
      -- Local instance justification (proof-local temporary data): bundled `S₂.isSquareZero` is not globally registered on the structure Solution.
      letI := S₂.isSquareZero
      let x := Function.surjInv Cotangent.mk_surjective f
      let f' := liftPoly π₁ x.1
      S₂.kernelEquiv (ofMem (Iff.mpr (mem_ker (f := S₂.toB) (r := evalBack D f'))
          (evalBack_lift_mem_ker D f))) -
        D.ν (S₁.kernelEquiv (ofMem (Iff.mpr (mem_ker (f := S₁.toB) (r := evalFront f'))
        (evalFront_lift_mem_ker D f)))) := by
  rfl

/-- The conormal representative is additive in its cotangent input. -/
theorem conormal_map_add (D : RelativeDiagram S₁ S₂)
    (f g : (Generators.self A₁ B₁).toExtension.Cotangent) :
    conormalHom D (f + g) = conormalHom D f + conormalHom D g := by
  letI := moduleRestrict D
  exact (conormalHom D).map_add f g

/-- The conormal representative is linear in its cotangent input. -/
theorem conormal_map_smul (D : RelativeDiagram S₁ S₂) (b : B₁)
    (f : (Generators.self A₁ B₁).toExtension.Cotangent) :
    -- Local instance justification (noncanonical choice): scalar multiplication on the codomain is the action restricted along D.g.
    letI := moduleRestrict D
    conormalHom D (b • f) = b • conormalHom D f := by
  letI := moduleRestrict D
  exact (conormalHom D).map_smul b f

/-- The coefficient group containing the canonical obstruction class. -/
abbrev ObstructionGroup (D : RelativeDiagram S₁ S₂) : Type u :=
  -- Local instance justification (noncanonical choice): the obstruction group uses the N₂ action restricted along D.g.
  letI := moduleRestrict D
  extOneNaiveCotangent A₁ B₁ N₂

/-- The canonical class in Ext¹_{B₁}(NL_{B₁/A₁}, N₂) attached to a relative diagram. -/
def mapObstruction (D : RelativeDiagram S₁ S₂) : ObstructionGroup D :=
  -- Local instance justification (noncanonical choice): constructing the class requires the N₂ action restricted along D.g.
  letI := moduleRestrict D
  extOneNaiveCotangent_mk A₁ B₁ N₂ (conormalHom D)

/-- `mapObstruction` is the class of `conormalHom`. -/
theorem mapObstruction_spec (D : RelativeDiagram S₁ S₂) :
    -- Local instance justification (noncanonical choice): the B₁-action on N₂ is restriction along D.g.
    letI := moduleRestrict D
    mapObstruction D = extOneNaiveCotangent_mk A₁ B₁ N₂ (conormalHom D) := by
  rfl

/-- Evaluation of a conormal representative on a relation and its polynomial lift. -/
theorem conormalHom_eval (D : RelativeDiagram S₁ S₂)
    (j : (Generators.self A₁ B₁).toExtension.ker)
    (p' : MvPolynomial B₁ A₁') (n₁ : N₁) (n₂ : N₂)
    (hp : MvPolynomial.map π₁ p' = j.1)
    (hn₁ :
      -- Local instance justification (proof-local temporary data): the front inclusion uses the ring structure stored in S₁.
      letI := S₁.commRing
      -- Local instance justification (proof-local temporary data): the front inclusion uses the square-zero structure stored in S₁.
      letI := S₁.isSquareZero
      Solution.inclusion π₁ c₁ S₁ n₁ = evalFront p')
    (hn₂ :
      -- Local instance justification (proof-local temporary data): the back inclusion uses the ring structure stored in S₂.
      letI := S₂.commRing
      -- Local instance justification (proof-local temporary data): the back inclusion uses the square-zero structure stored in S₂.
      letI := S₂.isSquareZero
      Solution.inclusion π₂ c₂ S₂ n₂ = evalBack D p') :
    -- Local instance justification (noncanonical choice): the conormal representative is valued in N₂ with the action restricted along D.g.
    letI := moduleRestrict D
    conormalHom D (Cotangent.mk j) = n₂ - D.ν n₁ := sorry

/-- A conormal representative computed from arbitrary valid generator lifts gives the canonical class. -/
theorem mapObstruction_eq_of_representative (D : RelativeDiagram S₁ S₂)
    (y : B₁ → S₁.carrier) (z : B₁ → S₂.carrier)
    (hy : ∀ b : B₁,
      -- Local instance justification (proof-local temporary data): the front projection is evaluated in S₁.carrier.
      letI := S₁.commRing
      S₁.toB (y b) = b)
    (hz : ∀ b : B₁,
      -- Local instance justification (proof-local temporary data): the back projection is evaluated in S₂.carrier.
      letI := S₂.commRing
      S₂.toB (z b) = D.g b)
    (f : ConormalMaps D)
    (hf : ∀ (j : (Generators.self A₁ B₁).toExtension.ker)
      (p' : MvPolynomial B₁ A₁') (n₁ : N₁) (n₂ : N₂),
      MvPolynomial.map π₁ p' = j.1 →
      (
        -- Local instance justification (defeq pin): polynomial evaluation must use the ring structure stored in S₁ so that its coefficient map is S₁.fromA'; Solution has no companion ring instance.
        letI := S₁.commRing
        -- Local instance justification (defeq pin): the front kernel inclusion must use the square-zero structure stored in S₁, matching S₁.kernelEquiv.
        letI := S₁.isSquareZero
        Solution.inclusion π₁ c₁ S₁ n₁ = eval₂Hom S₁.fromA' y p') →
      (
        -- Local instance justification (defeq pin): polynomial evaluation must use the ring structure stored in S₂ so that its coefficient map is S₂.fromA'.comp D.t'; Solution has no companion ring instance.
        letI := S₂.commRing
        -- Local instance justification (defeq pin): the back kernel inclusion must use the square-zero structure stored in S₂, matching S₂.kernelEquiv.
        letI := S₂.isSquareZero
        Solution.inclusion π₂ c₂ S₂ n₂ =
          eval₂Hom (S₂.fromA'.comp D.t') z p') →
      f (Cotangent.mk j) = n₂ - D.ν n₁) :
    -- Local instance justification (noncanonical choice): the representative comparison is valued in N₂ with the action restricted along D.g.
    letI := moduleRestrict D
    mapObstruction D = extOneNaiveCotangent_mk A₁ B₁ N₂ f := sorry

end RelativeDiagram

/-- The obstruction vanishes exactly when the relative diagram has a filler. -/
theorem mapObstruction_eq_zero_iff (D : RelativeDiagram S₁ S₂) :
    -- Local instance justification (noncanonical choice): the obstruction group uses N₂ restricted along D.g.
    letI := RelativeDiagram.moduleRestrict D
    RelativeDiagram.mapObstruction D = 0 ↔ Nonempty (FittingMap D) := sorry

end SquareZeroExtension

end RingHom
