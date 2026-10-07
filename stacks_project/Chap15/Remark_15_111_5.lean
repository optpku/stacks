module

import StacksCheckRecall
public import ReasLib.RingTheory.Invariant.FixedPoints.IdealQuotient.InvertibleCard

/-!
# Remark 15.111.5

@stack 0H36
-/

@[expose] public section

universe u v

/- Remark 15.111.5 (tag `0H36`):
if a finite group acts on a commutative ring `R` and `Nat.card G` is a unit in `R`, then for every
ideal `J` of `FixedPoints.subring R G`, the canonical map from
`FixedPoints.subring R G ⧸ J` to the fixed points of
`R ⧸ FixedPoints.Quotient.ideal J` is an isomorphism.
-/
@[stacks 0H36 "Remark 15.111.5"]
#check fun (R : Type u) (G : Type v) [CommRing R] [Group G]
    [MulSemiringAction G R] [Finite G]
    (J : Ideal (FixedPoints.subring R G))
    (h_card : IsUnit (Nat.card G : R)) ↦
  (FixedPoints.Quotient.map_bijective_of_isUnit_card J h_card :
    Function.Bijective (FixedPoints.Quotient.map J))
