module

public import ReasLib.RingTheory.Valuation.Extension
import StacksCheckRecall

@[expose] public section

/-!
# Definition 15.124.1

@stack 0ASG

This chapter file is a source-facing recall.  The reusable owner is
`ReasLib.RingTheory.Valuation.Extension`; the checks below keep all three
clauses of the source definition visible without creating a second class or a
second family of fraction-field instances in Chap15.
-/

-- Definition 15.124.1 (1): injective local maps of valuation rings.
@[stacks 0ASG "Definition 15.124.1 (1), extension of valuation rings"]
#check @IsExtensionOfValuationRings
#check @isExtensionOfValuationRings_iff

-- Definition 15.124.1 (2): bijectivity of the induced value-group map.
@[stacks 0ASG "Definition 15.124.1 (2), weakly unramified"]
#check @IsExtensionOfValuationRings.WeaklyUnramified
#check @IsExtensionOfValuationRings.WeaklyUnramified.spec

-- Definition 15.124.1 (3): residue degree.
@[stacks 0ASG "Definition 15.124.1 (3), residue degree"]
#check @IsExtensionOfValuationRings.residueDegree

-- Derived value-group quotient invariant and the canonical bridges used downstream.
#check @IsExtensionOfValuationRings.ramificationIndex
#check @IsExtensionOfValuationRings.integer_comap
#check @IsExtensionOfValuationRings.fractionRingValuativeExtension
#check @integralClosure_extension
#check @discreteValuationRingExtension_toIsExtensionOfValuationRings
