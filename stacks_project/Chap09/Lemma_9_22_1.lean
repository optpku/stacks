/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Galois.KrullTopology
import StacksCheckRecall

@[expose] public section

/- Lemma 9.22.1 (Tag 0BMJ): for a map into a Krull-topological Galois group, continuity of the
action on the discrete extension field implies continuity of the map; for a Galois extension, the
Galois group is the canonical profinite group `InfiniteGalois.profiniteGalGrp`. -/
#check FieldExtension.continuousSMulGalOfIsIntegral
#check FieldExtension.continuousOfContinuousGaloisEval
@[stacks 0BMJ]
#check FieldExtension.continuousOfContinuousGaloisAction
#check InfiniteGalois.profiniteGalGrp
