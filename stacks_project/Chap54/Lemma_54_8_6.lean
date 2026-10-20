module

public import ReasLib.RingTheory.Normal.ReductionPossible
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 54.8.6: a finite injective local map between two-dimensional local normal Nagata
domains with separable induced fraction-field extension transfers reduction to rational
singularities from `A` to `B`. -/
@[stacks 0AXL] #check (RationalSingularity.ReductionPossible.ascend :
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [NagataRing B] [_root_.IsNormalRing B]
    [RationalSingularity.ReductionPossible A]
    (h_injective : Function.Injective (algebraMap A B))
    (h_dimension_B : ringKrullDim B = 2)
    (h_separable : FractionRing.isSeparableOf h_injective),
    RationalSingularity.ReductionPossible B)
