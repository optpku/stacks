/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Polynomial.Basic
public import ReasLib.Algebra.Module.Reflexive.Relative

/-!
# Ordinary and relative reflexivity can differ

This file gives an explicit numerical semigroup ring whose dualizing ideal is reflexive relative
to itself but is not reflexive with respect to the ring.
-/

@[expose] public section

universe u

namespace Module.RelativeReflexivityCounterexample

-- The algebra and ideal structures over an arbitrary field are not computable uniformly.
noncomputable section

variable (k : Type u) [Field k]

/-- The subalgebra `k[t³, t⁴, t⁵]` of the polynomial ring `k[t]`. -/
def ring : Subalgebra k (Polynomial k) :=
  Algebra.adjoin k
    ({(Polynomial.X : Polynomial k) ^ 3, (Polynomial.X : Polynomial k) ^ 4,
      (Polynomial.X : Polynomial k) ^ 5} : Set (Polynomial k))

/-- The ideal `(t³, t⁴)` in the numerical semigroup ring `k[t³, t⁴, t⁵]`. -/
def dualizingIdeal : Ideal (ring k) :=
  Ideal.span
    ({(⟨(Polynomial.X : Polynomial k) ^ 3, Algebra.subset_adjoin (by simp)⟩ : ring k),
      (⟨(Polynomial.X : Polynomial k) ^ 4, Algebra.subset_adjoin (by simp)⟩ : ring k)} :
      Set (ring k))

/-- The ideal `(t³, t⁴)` is not reflexive with respect to its numerical semigroup ring. -/
theorem dualizingIdeal_not_isReflexive :
    ¬ Module.IsReflexive (ring k) (dualizingIdeal k) := sorry

/-- The ideal `(t³, t⁴)` is reflexive relative to itself. -/
theorem dualizingIdeal_isReflexiveRelativeTo :
    Module.IsReflexiveRelativeTo (ring k) (dualizingIdeal k) (dualizingIdeal k) := sorry

/-- The ideal `(t³, t⁴)` over `k[t³, t⁴, t⁵]` separates ordinary reflexivity from
reflexivity relative to the dualizing ideal. -/
theorem dualizingIdeal_reflexivity_counterexample :
    ¬ Module.IsReflexive (ring k) (dualizingIdeal k) ∧
      Module.IsReflexiveRelativeTo (ring k) (dualizingIdeal k) (dualizingIdeal k) :=
  ⟨dualizingIdeal_not_isReflexive k, dualizingIdeal_isReflexiveRelativeTo k⟩

end

end RelativeReflexivityCounterexample

end Module
