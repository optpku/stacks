module

public import ReasLib.Topology.Algebra.OpenMapping
import StacksCheckRecall

/-!
# Lemma 15.36.5 (Open mapping lemma) (0CQW)

@stack 0CQW
-/

@[expose] public section

/- Lemma 15.36.5 (Open mapping lemma) (0CQW): exactly one of openness and a
nowhere-dense image of an open subgroup occurs. -/
@[stacks 0CQW]
#check @ContinuousAddMonoidHom.isOpenMap_xor_exists_nowhereDense_image
