/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Determinant
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ModuleEnd
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Two-periodic complexes from invertible upper-right matrix blocks

This file constructs an exact two-periodic complex from two invertible matrices placed in
the upper-right blocks of square-zero endomorphisms and states its determinant formula.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.TwoPeriodicEndomorphism.UpperRightBlock

variable {k : Type u} [Field k]

/-- The endomorphism whose matrix has `U` as its upper-right block and zero in
the other three blocks. -/
def endomorphism {a : ℕ} (U : Matrix.GeneralLinearGroup (Fin a) k) :
    Module.End k (Fin a ⊕ Fin a → k) :=
  Matrix.toLin' (Matrix.fromBlocks 0 U 0 0)

/-- The upper-right block endomorphism applies `U` to the right coordinates and
has zero right component. -/
@[simp]
theorem endomorphism_apply {a : ℕ} (U : Matrix.GeneralLinearGroup (Fin a) k)
    (x : Fin a ⊕ Fin a → k) :
    endomorphism U x =
      Sum.elim (fun i ↦ ∑ j, U i j * x (Sum.inr j)) (fun _ ↦ 0) := sorry

/-- The range of one invertible upper-right block endomorphism is the kernel of
any other such endomorphism. -/
theorem range_eq_ker {a : ℕ} (U V : Matrix.GeneralLinearGroup (Fin a) k) :
    (endomorphism U).range = (endomorphism V).ker := sorry

/-- The exact two-periodic complex with upper-right blocks `U` and `V`. -/
def complex {a : ℕ} (U V : Matrix.GeneralLinearGroup (Fin a) k) :
    TwoPeriodicEndomorphism (ModuleCat k) :=
  ofModuleEnd (endomorphism U) (endomorphism V)
    (range_eq_ker U V).le (range_eq_ker V U).le

/-- The carrier of `complex U V` is the sum-indexed coordinate module. -/
@[simp]
theorem complex_X {a : ℕ} (U V : Matrix.GeneralLinearGroup (Fin a) k) :
    (complex U V).X = ModuleCat.of k (Fin a ⊕ Fin a → k) := sorry

/-- The degree-zero differential of `complex U V` is the endomorphism with
upper-right block `U`. -/
@[simp]
theorem complex_d₀ {a : ℕ} (U V : Matrix.GeneralLinearGroup (Fin a) k) :
    (complex U V).d₀ = ModuleCat.ofHom (endomorphism U) := sorry

/-- The degree-one differential of `complex U V` is the endomorphism with
upper-right block `V`. -/
@[simp]
theorem complex_d₁ {a : ℕ} (U V : Matrix.GeneralLinearGroup (Fin a) k) :
    (complex U V).d₁ = ModuleCat.ofHom (endomorphism V) := sorry

/-- The carrier of the upper-right block complex has finite length over `k`. -/
theorem complex_isFiniteLength {a : ℕ}
    (U V : Matrix.GeneralLinearGroup (Fin a) k) :
    IsFiniteLength k (complex U V).X := sorry

/-- The upper-right block complex is acyclic. -/
theorem complex_acyclic {a : ℕ} (U V : Matrix.GeneralLinearGroup (Fin a) k) :
    (complex U V).toCochainComplex.Acyclic := sorry

/-- For invertible `a × a` matrices `U` and `V`, the determinant of the exact
two-periodic complex with upper-right blocks `U` and `V` is the residue-field image of
`(-1) ^ a * det U / det V`. -/
theorem determinant_eq {a : ℕ} (U V : Matrix.GeneralLinearGroup (Fin a) k) :
    determinant (complex U V) (complex_isFiniteLength U V) (complex_acyclic U V) =
      Units.map (IsLocalRing.residue k).toMonoidHom
        (((-1 : kˣ) ^ a) * Matrix.GeneralLinearGroup.det U /
          Matrix.GeneralLinearGroup.det V) := sorry

end CategoryTheory.TwoPeriodicEndomorphism.UpperRightBlock
