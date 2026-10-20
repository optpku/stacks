module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.FieldRamification
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.TotalRamification
import StacksCheckRecall

@[expose] public section

/-!
# Definition 15.112.7

For a finite separable extension of the fraction field of a discrete valuation ring, the three
ramification conditions are the canonical field-model predicates below.  Their owners keep the
fraction-field model explicit and expose the branchwise residue-field and ramification-index
conditions through `spec` and `iff_forall` APIs.

@stack 09E9
-/

universe u v w

/- Definition 15.112.7 (1): unramified extensions over a discrete valuation ring. -/
@[stacks 09E9 "Definition 15.112.7 (1): unramified extension"]
#check fun (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] ↦
  (DVR.Field.IsUnramified A K L : Prop)

/- Definition 15.112.7 (2): tamely ramified extensions over a discrete valuation ring. -/
@[stacks 09E9 "Definition 15.112.7 (2): tamely ramified extension"]
#check fun (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] ↦
  (DVR.Field.IsTamelyRamified A K L : Prop)

/- Definition 15.112.7 (3): totally ramified extensions over a discrete valuation ring. -/
@[stacks 09E9 "Definition 15.112.7 (3): totally ramified extension"]
#check fun (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] ↦
  (DVR.Field.IsTotallyRamified A K L : Prop)

end
