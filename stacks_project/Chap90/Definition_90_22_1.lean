module

public import stacks_project.Chap90.Definition_90_22_1_Prorepresentable
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Definition 90.22.1: a groupoid in functors on `ArtinianLocalAlgCat Λ k` is prorepresentable
if it is isomorphic to the restriction of a representable groupoid in functors
`(coyoneda.obj (op R0), coyoneda.obj (op R1), s, t, c)` on `CompleteLocalAlgCat Λ k`. -/
@[stacks 06KD]
#check GroupoidInFunctors.IsProrepresentable
