module

import ReasLib.RingTheory.LocalRing.TameSymbol.DiscreteValuationRing.Determinant
import StacksCheckRecall

@[expose] public section

universe u v

variable (A : Type u) (K : Type v) [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]
  (x y : Kˣ)

/- Lemma 42.68.37: the determinant construction of the tame symbol over a discrete
valuation ring equals the residue of the signed crossed-order ratio. -/
@[stacks 02Q6] #check
  (DVR.TameSymbol.determinant_eq_value A K x y :
    DVR.TameSymbol.determinantValue A K x y = DVR.TameSymbol.value A K x y)
