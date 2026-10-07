module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CurveDuality
public import stacks_project.Chap64.Proposition_64_29_3_AssociatedSheaf
public import stacks_project.Chap64.Proposition_64_29_3_AmbientAcyclicity
public import stacks_project.Chap64.Proposition_64_29_3_AmbientCohomology
public import stacks_project.Chap64.Proposition_64_29_3_GeometricInvariants
public import stacks_project.Chap64.Proposition_64_29_3_CompletedGroupRingAlgebra
import StacksCheckRecall

/-!
The residual group over an arbitrary field is its absolute Galois group.
Compact homological degree i is placed in cohomological degree 2-i.
For left coefficients the tensor order is Lambda tensor M(-1).
-/

/- Proposition 64.29.3 (1). The actual compact-support evaluation and trace
give a natural derived isomorphism to completed tensor, for arbitrary finite rings. -/
@[stacks 03VM]
#check SourceFaithful03VM.compactNaturalIso

/- Proposition 64.29.3 (2). Taking degree 2-i gives compact group homology
with the inverse Tate twist and the same residual action. -/
@[stacks 03VM]
#check SourceFaithful03VM.compactDegreeIso

/- Proposition 64.29.3 (3). Geometric sections identify naturally with
geometric invariants in the all-discrete ambient category. -/
@[stacks 03VM]
#check SourceFaithful03VM.ordinaryZeroIso

/- Proposition 64.29.3 (4). The higher comparison is the canonical natural
derived-invariants comparison under curve-specific effacement. -/
@[stacks 03VM]
#check SourceFaithful03VM.ordinaryDegreeIso

/- Proposition 64.29.3 (5). The ordinary comparison retains the completed
residual Galois action on the actual published associated sheaf. -/
@[stacks 03VM]
#check SourceFaithful03VM.ordinaryDerivedIso

/- Proposition 64.29.3 (6). For finite ground fields only, arithmetic Frobenius
transports the same derived comparison to the profinite-integer residual group. -/
@[stacks 03VM]
#check SourceFaithful03VM.finiteFieldIso
