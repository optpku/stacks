module

public import stacks_project.Chap92.Lemma_92_25_1_Fibered
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.Scheme.CotangentSite

/- Lemma 92.25.1: in the situation above the category `Obj Λ X` is fibred over
`X.smallZariskiSite` via the forgetful functor `forgetZariski`. -/
@[stacks 08V9] #check forgetZariski_isFibered
