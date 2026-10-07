module

public import stacks_project.Chap67.Definition_67_47_7_Birational
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 67.47.8: Let `S` be a scheme. Let `X` and `Y` be algebraic spaces over `S`
with `|X|` and `|Y|` irreducible. Then `X` and `Y` are birational if and only if there
are nonempty open subspaces `U ⊂ X` and `V ⊂ Y` which are isomorphic as algebraic
spaces over `S`. -/
@[stacks 0EMU] #check AlgebraicGeometry.AlgebraicSpace.birational_iff_nonempty_open
