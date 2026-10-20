module

public import ReasLib.RingTheory.Normal.ReductionPossible
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 54.8.10: let `p` be prime and let `A` be a complete regular local ring of
dimension two and characteristic `p`. If `L` is an inseparable extension of degree `p`
of a fraction field `K` of `A`, then reduction to rational singularities is possible for
the integral closure of `A` in `L`. -/
@[stacks 0B4U] #check
  (RationalSingularity.ReductionPossible.ofIntegralClosureInseparableDegreePrime :
    ∀ (p : ℕ) (hp : p.Prime)
    (A : Type u) [CommRing A] [IsCompleteLocalRing A] [IsRegularLocalRing A]
    [CharP A p] (h_dimension : ringKrullDim A = 2)
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] (h_degree : Module.finrank K L = p)
    (h_inseparable : ¬ Algebra.IsSeparable K L),
    RationalSingularity.ReductionPossible (integralClosure A L))
