module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Residue
import StacksCheckRecall

@[expose] public section

/-!
# Definition 15.112.1

Compatibility entry point for the reusable API of extensions of discrete
valuation rings. The owners are split by mathematical layer under
`ReasLib.RingTheory.DiscreteValuationRing.Extension`.

@stack 09E4
-/

/- Definition 15.112.1 (1), tag `09E4`: extensions of discrete valuation rings. -/
@[stacks 09E4 "(1), DVR extension"]
#check @IsExtensionOfDiscreteValuationRings

/- Definition 15.112.1 (2): the ramification index is the positive exponent describing the image
of the source maximal ideal. -/
@[stacks 09E4 "(2), ramification index"]
#check @IsExtensionOfDiscreteValuationRings.ramificationIndex

#check @IsExtensionOfDiscreteValuationRings.ramificationIndex_eq_iff

/- Definition 15.112.1 (3): a DVR extension is weakly unramified exactly when its ramification
index is one. -/
@[stacks 09E4 "(3), weakly unramified extension"]
#check @IsExtensionOfDiscreteValuationRings.WeaklyUnramified

/- Definition 15.112.1 (4): the residue degree is the finite dimension of the residue-field
extension. -/
@[stacks 09E4 "(4), residue degree"]
#check @IsExtensionOfDiscreteValuationRings.residueDegree

#check @IsExtensionOfDiscreteValuationRings.residueDegree_eq_finrank
