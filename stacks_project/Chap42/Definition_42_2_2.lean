/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Multiplicity
import StacksCheckRecall

universe u v

/- Definition 42.2.2 (1): the multiplicity of a `ZMod 2`-indexed complex with finite-length
homology is the degree-zero homology length minus the degree-one homology length. -/
@[stacks 02PH] #check (CategoryTheory.CochainComplex.multiplicity :
  ∀ {R : Type u} [Ring R] (K : CochainComplex (ModuleCat.{v} R) (ZMod 2)),
    IsFiniteLength R (K.homology 0) → IsFiniteLength R (K.homology 1) → ℤ)

/- Definition 42.2.2 (2): for a two-periodic endomorphism, the same multiplicity is also
called the additive Herbrand quotient. -/
@[stacks 02PH] #check (CategoryTheory.TwoPeriodicEndomorphism.multiplicity :
  ∀ {R : Type u} [Ring R]
    (K : CategoryTheory.TwoPeriodicEndomorphism (ModuleCat.{v} R)),
    IsFiniteLength R (K.toCochainComplex.homology 0) →
      IsFiniteLength R (K.toCochainComplex.homology 1) → ℤ)
