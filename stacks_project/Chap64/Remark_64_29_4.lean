module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CurvePairing
import StacksCheckRecall

/- Remark 64.29.4 (1). The specified geometric evaluation and normalized
trace give the perfect compact-support pairing with ordinary cohomology of
the intrinsic right dual, canonically the character/Tate coefficient. -/
@[stacks 03VN]
#check SourceFaithful03VN.compactSupportPairing_bijective

/- Remark 64.29.4 (2). For projective curves the actual identity-extension
counit identifies compact and ordinary cohomology, giving Poincare duality. -/
@[stacks 03VN]
#check SourceFaithful03VN.projectivePairing_bijective
