/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import ReasLib.RingTheory.FiniteFree
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite Freeness of the Elementary-Symmetric Extension

The canonical fundamental-theorem map identifies a polynomial coefficient ring with the symmetric
subalgebra.  Composing it with the subalgebra inclusion gives the elementary-symmetric extension;
the finite-free property is stated at the ring-map level so downstream users need no theorem-local
`Algebra` construction.
-/

@[expose] public section

universe u v

namespace MvPolynomial.ElementarySymmetric

/-- The elementary-symmetric coefficient map for a finite variable type. -/
@[stacks 00SR "elementary-symmetric coefficient map"]
noncomputable def algHom (R : Type u) (σ : Type v) [CommRing R] [Fintype σ] :
    MvPolynomial (Fin (Fintype.card σ)) R →ₐ[R] MvPolynomial σ R :=
  (symmetricSubalgebra σ R).val.comp
    (esymmAlgHom σ R (Fintype.card σ))

/-- The elementary-symmetric map sends the `i`-th coefficient variable to the corresponding
elementary symmetric polynomial. -/
@[simp, stacks 00SR "elementary-symmetric coefficient generator"]
theorem algHom_apply_X (R : Type u) (σ : Type v) [CommRing R] [Fintype σ]
    (i : Fin (Fintype.card σ)) :
    algHom R σ (X i) = esymm σ R (i + 1) := sorry

/-- The elementary-symmetric extension with the canonical finite index type. -/
@[stacks 00SR "Fin-indexed elementary-symmetric coefficient map"]
noncomputable def algHomFin (R : Type u) (n : ℕ) [CommRing R] :
    MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  (symmetricSubalgebra (Fin n) R).val.comp
    (esymmAlgHom (Fin n) R n)

/-- The `Fin`-indexed elementary-symmetric map sends a coefficient variable to an elementary
symmetric polynomial. -/
@[simp, stacks 00SR "Fin-indexed elementary-symmetric generator"]
theorem algHomFin_apply_X (R : Type u) (n : ℕ) [CommRing R] (i : Fin n) :
    algHomFin R n (X i) = esymm (Fin n) R (i + 1) := sorry

/-- The elementary-symmetric extension is finite free over its coefficient ring. -/
@[stacks 00SR "elementary-symmetric finite-free extension"]
theorem finiteFree (R : Type u) (σ : Type v) [CommRing R] [Fintype σ] :
    (algHom R σ).toRingHom.FiniteFree := sorry

/-- The canonical `Fin`-indexed elementary-symmetric extension is finite free. -/
@[stacks 00SR "Fin-indexed elementary-symmetric finite-free extension"]
theorem finiteFreeFin (R : Type u) (n : ℕ) [CommRing R] :
    (algHomFin R n).toRingHom.FiniteFree := sorry

end MvPolynomial.ElementarySymmetric
