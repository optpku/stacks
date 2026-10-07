module

public import ReasLib.RingTheory.Ideal.AssociatedGraded.Hilbert
public import ReasLib.RingTheory.Ideal.AssociatedGraded.StageClass
import StacksCheckRecall

/-!
# Homogeneous-Piece Support for Lemma 10.106.1

The successive-quotient comparison and its residue-field-linear form belong
to the general associated-graded API.  No regular-local specialization is
needed in this source-facing file.

@stack 00NO
-/

@[expose] public section

@[stacks 00NO "homogeneous grade and successive quotient"]
#check @Ideal.AssociatedGraded.gradeEquivPiece

@[stacks 00NO "residue-field-linear homogeneous comparison"]
#check @Ideal.AssociatedGraded.gradeEquivPieceResidueField

@[stacks 00NO "comparison on a stage class"]
#check @Ideal.AssociatedGraded.gradeEquivPieceResidueField_stageClassLinear

@[stacks 00NO "associated-graded piece Hilbert value"]
#check @Ideal.AssociatedGraded.piece_length_eq_phi
