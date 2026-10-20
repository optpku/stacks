module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Hom.Determinant.ShortExact
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ModuleEnd
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Complementary diagonal two-periodic complexes

This file constructs exact two-periodic complexes whose differentials are
diagonal on complementary coordinate summands and states their determinant formula.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped BigOperators

universe u

namespace CategoryTheory.TwoPeriodicEndomorphism.ComplementaryDiagonal

variable {k : Type u} [Field k]

/-- The diagonal endomorphism with entries `u` on the left summand and zero on
the right summand. -/
def phi {a b : ℕ} (u : Fin a → kˣ) : Module.End k (Fin a ⊕ Fin b → k) :=
  Matrix.toLin' (Matrix.diagonal (Sum.elim (fun i ↦ (u i : k)) (fun _ ↦ 0)))

/-- The coordinate action of `phi`. -/
@[simp]
theorem phi_apply {a b : ℕ} (u : Fin a → kˣ) (x : Fin a ⊕ Fin b → k) :
    phi u x = Sum.elim (fun i ↦ u i * x (Sum.inl i)) (fun _ ↦ 0) := sorry

/-- The diagonal endomorphism that is zero on the left summand and has entries
`v` on the right summand. -/
def psi {a b : ℕ} (v : Fin b → kˣ) : Module.End k (Fin a ⊕ Fin b → k) :=
  Matrix.toLin' (Matrix.diagonal (Sum.elim (fun _ ↦ 0) (fun j ↦ (v j : k))))

/-- The coordinate action of `psi`. -/
@[simp]
theorem psi_apply {a b : ℕ} (v : Fin b → kˣ) (x : Fin a ⊕ Fin b → k) :
    psi v x = Sum.elim (fun _ ↦ 0) (fun j ↦ v j * x (Sum.inr j)) := sorry

/-- The range of `phi u` is the kernel of `psi v`. -/
theorem phi_range_eq_psi_ker {a b : ℕ} (u : Fin a → kˣ) (v : Fin b → kˣ) :
    (phi u).range = (psi v).ker := sorry

/-- The range of `psi v` is the kernel of `phi u`. -/
theorem psi_range_eq_phi_ker {a b : ℕ} (u : Fin a → kˣ) (v : Fin b → kˣ) :
    (psi v).range = (phi u).ker := sorry

/-- The exact two-periodic complex with complementary diagonal differentials. -/
def complex {a b : ℕ} (u : Fin a → kˣ) (v : Fin b → kˣ) :
    TwoPeriodicEndomorphism (ModuleCat k) :=
  ofModuleEnd (phi u) (psi v)
    (phi_range_eq_psi_ker u v).le (psi_range_eq_phi_ker u v).le

/-- The carrier of `complex u v` is the sum-indexed coordinate module. -/
@[simp]
theorem complex_X {a b : ℕ} (u : Fin a → kˣ) (v : Fin b → kˣ) :
    (complex u v).X = ModuleCat.of k (Fin a ⊕ Fin b → k) := sorry

/-- The degree-zero differential of `complex u v` is `phi u`. -/
@[simp]
theorem complex_d₀ {a b : ℕ} (u : Fin a → kˣ) (v : Fin b → kˣ) :
    (complex u v).d₀ = ModuleCat.ofHom (phi u) := sorry

/-- The degree-one differential of `complex u v` is `psi v`. -/
@[simp]
theorem complex_d₁ {a b : ℕ} (u : Fin a → kˣ) (v : Fin b → kˣ) :
    (complex u v).d₁ = ModuleCat.ofHom (psi v) := sorry

/-- The carrier of the complementary diagonal complex has finite length over
`k`. -/
theorem complex_isFiniteLength {a b : ℕ} (u : Fin a → kˣ) (v : Fin b → kˣ) :
    IsFiniteLength k (complex u v).X := sorry

/-- The complementary diagonal complex is acyclic. -/
theorem complex_acyclic {a b : ℕ} (u : Fin a → kˣ) (v : Fin b → kˣ) :
    (complex u v).toCochainComplex.Acyclic := sorry

/-- The determinant of the exact complementary diagonal complex is the residue-field
image of the product of the left diagonal entries divided by the product of the right
diagonal entries. -/
theorem determinant_eq {a b : ℕ} (u : Fin a → kˣ) (v : Fin b → kˣ) :
    determinant (complex u v) (complex_isFiniteLength u v) (complex_acyclic u v) =
      Units.map (IsLocalRing.residue k).toMonoidHom
        ((∏ i, u i) / (∏ j, v j)) := sorry

end CategoryTheory.TwoPeriodicEndomorphism.ComplementaryDiagonal
