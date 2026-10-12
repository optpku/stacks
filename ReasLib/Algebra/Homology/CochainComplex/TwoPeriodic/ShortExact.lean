/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Multiplicity
import Mathlib.Algebra.Homology.HomologySequence

/-!
# Short Exact Sequences of Two-Periodic Complexes

This file records finite-length and multiplicity consequences of a short exact sequence of
two-periodic cochain complexes of modules.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace CategoryTheory.ShortComplex.ShortExact

variable {R : Type u} [Ring R]
variable {S : ShortComplex (CochainComplex (ModuleCat.{v} R) (ZMod 2))}

/-- If the middle and right complexes in a short exact sequence of two-periodic complexes
have finite-length homology in both degrees, then so does the left complex. -/
theorem finiteHomology_X₁ (hS : S.ShortExact)
    (h₂₀ : IsFiniteLength R (S.X₂.homology 0))
    (h₂₁ : IsFiniteLength R (S.X₂.homology 1))
    (h₃₀ : IsFiniteLength R (S.X₃.homology 0))
    (h₃₁ : IsFiniteLength R (S.X₃.homology 1)) :
    IsFiniteLength R (S.X₁.homology 0) ∧ IsFiniteLength R (S.X₁.homology 1) := sorry

/-- If the left and right complexes in a short exact sequence of two-periodic complexes
have finite-length homology in both degrees, then so does the middle complex. -/
theorem finiteHomology_X₂ (hS : S.ShortExact)
    (h₁₀ : IsFiniteLength R (S.X₁.homology 0))
    (h₁₁ : IsFiniteLength R (S.X₁.homology 1))
    (h₃₀ : IsFiniteLength R (S.X₃.homology 0))
    (h₃₁ : IsFiniteLength R (S.X₃.homology 1)) :
    IsFiniteLength R (S.X₂.homology 0) ∧ IsFiniteLength R (S.X₂.homology 1) := sorry

/-- If the left and middle complexes in a short exact sequence of two-periodic complexes
have finite-length homology in both degrees, then so does the right complex. -/
theorem finiteHomology_X₃ (hS : S.ShortExact)
    (h₁₀ : IsFiniteLength R (S.X₁.homology 0))
    (h₁₁ : IsFiniteLength R (S.X₁.homology 1))
    (h₂₀ : IsFiniteLength R (S.X₂.homology 0))
    (h₂₁ : IsFiniteLength R (S.X₂.homology 1)) :
    IsFiniteLength R (S.X₃.homology 0) ∧ IsFiniteLength R (S.X₃.homology 1) := sorry

/-- The degree-zero-minus-degree-one homology multiplicity is additive in a short exact
sequence of two-periodic complexes whose homology modules have finite length. -/
theorem multiplicity_eq_add (hS : S.ShortExact)
    (h₁₀ : IsFiniteLength R (S.X₁.homology 0))
    (h₁₁ : IsFiniteLength R (S.X₁.homology 1))
    (h₂₀ : IsFiniteLength R (S.X₂.homology 0))
    (h₂₁ : IsFiniteLength R (S.X₂.homology 1))
    (h₃₀ : IsFiniteLength R (S.X₃.homology 0))
    (h₃₁ : IsFiniteLength R (S.X₃.homology 1)) :
    CochainComplex.multiplicity S.X₂ h₂₀ h₂₁ =
      CochainComplex.multiplicity S.X₁ h₁₀ h₁₁ +
        CochainComplex.multiplicity S.X₃ h₃₀ h₃₁ := sorry

end CategoryTheory.ShortComplex.ShortExact
