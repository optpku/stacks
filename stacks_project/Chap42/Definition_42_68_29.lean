/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Lemma_42_68_28
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant
import StacksCheckRecall

universe u v

/- Definition 42.68.29: the symbol `d_M(a, b)` is the determinant unit of the
two-periodic scalar quotient of `M` by `a * b`. -/
@[stacks 02PZ] #check
  (CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientDeterminant :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
      (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
      (hdim : Module.supportDim A M = 1),
      (IsLocalRing.ResidueField A)ˣ)
