/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ShortExact
import StacksCheckRecall

@[expose] public section

universe u v

open CategoryTheory

/- Lemma 42.2.3 (1): if the middle and right two-periodic complexes have finite-length
cohomology, then so does the left complex. -/
@[stacks 0EA7] #check
  (CategoryTheory.ShortComplex.ShortExact.finiteHomology_X₁ :
    ∀ {R : Type u} [Ring R]
      {S : ShortComplex (CochainComplex (ModuleCat.{v} R) (ZMod 2))},
      S.ShortExact →
        IsFiniteLength R (S.X₂.homology 0) →
        IsFiniteLength R (S.X₂.homology 1) →
        IsFiniteLength R (S.X₃.homology 0) →
        IsFiniteLength R (S.X₃.homology 1) →
        IsFiniteLength R (S.X₁.homology 0) ∧ IsFiniteLength R (S.X₁.homology 1))

/- Lemma 42.2.3 (2): if the left and right two-periodic complexes have finite-length
cohomology, then so does the middle complex. -/
@[stacks 0EA7] #check
  (CategoryTheory.ShortComplex.ShortExact.finiteHomology_X₂ :
    ∀ {R : Type u} [Ring R]
      {S : ShortComplex (CochainComplex (ModuleCat.{v} R) (ZMod 2))},
      S.ShortExact →
        IsFiniteLength R (S.X₁.homology 0) →
        IsFiniteLength R (S.X₁.homology 1) →
        IsFiniteLength R (S.X₃.homology 0) →
        IsFiniteLength R (S.X₃.homology 1) →
        IsFiniteLength R (S.X₂.homology 0) ∧ IsFiniteLength R (S.X₂.homology 1))

/- Lemma 42.2.3 (3): if the left and middle two-periodic complexes have finite-length
cohomology, then so does the right complex. -/
@[stacks 0EA7] #check
  (CategoryTheory.ShortComplex.ShortExact.finiteHomology_X₃ :
    ∀ {R : Type u} [Ring R]
      {S : ShortComplex (CochainComplex (ModuleCat.{v} R) (ZMod 2))},
      S.ShortExact →
        IsFiniteLength R (S.X₁.homology 0) →
        IsFiniteLength R (S.X₁.homology 1) →
        IsFiniteLength R (S.X₂.homology 0) →
        IsFiniteLength R (S.X₂.homology 1) →
        IsFiniteLength R (S.X₃.homology 0) ∧ IsFiniteLength R (S.X₃.homology 1))

/- Lemma 42.2.3 (4): multiplicity is additive in a short exact sequence of two-periodic
complexes with finite-length cohomology. -/
@[stacks 0EA7] #check
  (CategoryTheory.ShortComplex.ShortExact.multiplicity_eq_add :
    ∀ {R : Type u} [Ring R]
      {S : ShortComplex (CochainComplex (ModuleCat.{v} R) (ZMod 2))}
      (hS : S.ShortExact)
      (h₁₀ : IsFiniteLength R (S.X₁.homology 0))
      (h₁₁ : IsFiniteLength R (S.X₁.homology 1))
      (h₂₀ : IsFiniteLength R (S.X₂.homology 0))
      (h₂₁ : IsFiniteLength R (S.X₂.homology 1))
      (h₃₀ : IsFiniteLength R (S.X₃.homology 0))
      (h₃₁ : IsFiniteLength R (S.X₃.homology 1)),
      CochainComplex.multiplicity S.X₂ h₂₀ h₂₁ =
        CochainComplex.multiplicity S.X₁ h₁₀ h₁₁ +
          CochainComplex.multiplicity S.X₃ h₃₀ h₃₁)
