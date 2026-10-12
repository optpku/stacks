/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Isomorphisms
public import ReasLib.LinearAlgebra.QuotientByIdeal.Scalar
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite free modules over quotient rings

@stack 0BC5

This leaf owns coordinatewise reduction of `Fin n → R` and the resulting quotient equivalence
with `Fin n → R ⧸ I`.
-/

@[expose] public section

noncomputable section

universe u

namespace Ideal.Quotient.Pi

variable {R : Type u} [Ring R] (I : Ideal R) [I.IsTwoSided]

/-- Coordinatewise reduction of a finite free module modulo `I`. -/
@[stacks 0BC5 "coordinatewise quotient map"]
noncomputable def coeffMap (n : ℕ) :
    (Fin n → R) →ₗ[R] (Fin n → R ⧸ I) :=
  LinearMap.pi fun i ↦ I.mkQ.comp (LinearMap.proj i)

/-- Coordinatewise reduction applies the quotient map in every coordinate. -/
@[simp, stacks 0BC5 "coordinatewise quotient map on entries"]
theorem coeffMap_apply (n : ℕ) (x : Fin n → R) (i : Fin n) :
    coeffMap I n x i = Ideal.Quotient.mk I (x i) :=
  rfl

/-- The kernel of coordinatewise reduction is the ideal multiple `I • ⊤`. -/
@[stacks 0BC5 "kernel of coordinatewise reduction"]
theorem ker_coeffMap (n : ℕ) :
    LinearMap.ker (coeffMap I n) = I • (⊤ : Submodule R (Fin n → R)) := by
  ext x
  constructor
  · intro hx
    have hxi (i : Fin n) : x i ∈ I := by
      have hi := congrFun (LinearMap.mem_ker.mp hx) i
      simpa only [coeffMap_apply, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem] using hi
    rw [← LinearMap.sum_single_apply (fun _ : Fin n ↦ R) x]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    have hi := Submodule.smul_mem_smul (hxi i)
      (show Pi.single i 1 ∈ (⊤ : Submodule R (Fin n → R)) from Submodule.mem_top)
    have heq : x i • Pi.single i (1 : R) = Pi.single i (x i) := by
      rw [← Pi.single_smul', smul_eq_mul, mul_one]
    rwa [heq] at hi
  · intro hx
    rw [LinearMap.mem_ker]
    funext i
    rw [coeffMap_apply, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha y _
      simpa [Pi.smul_apply, smul_eq_mul] using I.mul_mem_right (y i) ha
    · intro y z hy hz
      exact I.add_mem hy hz

/-- Coordinatewise reduction onto the finite free quotient module is surjective. -/
@[stacks 0BC5 "coordinatewise reduction is surjective"]
theorem coeffMap_surjective (n : ℕ) : Function.Surjective (coeffMap I n) := by
  intro y
  choose x hx using fun i ↦ Ideal.Quotient.mk_surjective (y i)
  refine ⟨x, funext fun i ↦ ?_⟩
  simpa only [coeffMap_apply] using hx i

/-- Quotienting `Fin n → R` by `I • ⊤` gives the finite free `R ⧸ I`-module. -/
@[stacks 0BC5 "finite free quotient equivalence"]
noncomputable def quotientLinearEquiv (n : ℕ) :
    ((Fin n → R) ⧸ (I • (⊤ : Submodule R (Fin n → R)))) ≃ₗ[R]
      (Fin n → R ⧸ I) :=
  (Submodule.quotEquivOfEq _ _ (ker_coeffMap I n).symm).trans <|
    (coeffMap I n).quotKerEquivRange.trans <|
      (LinearEquiv.ofEq _ _ (LinearMap.range_eq_top.2 (coeffMap_surjective I n))).trans
        Submodule.topEquiv

/-- `quotientLinearEquiv` sends a quotient representative to its coordinatewise reduction. -/
@[simp, stacks 0BC5 "finite free quotient equivalence on representatives"]
theorem quotientLinearEquiv_apply_mk (n : ℕ) (x : Fin n → R) :
    quotientLinearEquiv I n (Submodule.Quotient.mk x) = coeffMap I n x := by
  rfl

end Ideal.Quotient.Pi
