module

public import stacks_project.Chap94.Lemma_94_13_1_Instances
import StacksCheckRecall

@[expose] public section

/- Lemma 94.13.1 (1): let `S` be a scheme contained in `Sch_fppf`. A category
fibred in groupoids `X` over `(Sch/S)_fppf` which is representable by an
algebraic space is a Deligne-Mumford stack. -/
@[stacks 03YS]
#check @AlgebraicGeometry.DeligneMumfordStack.of_isRepresentableByAlgebraicSpace

/- Lemma 94.13.1 (2): if `F` is an algebraic space over `S`, then the associated
category fibred in groupoids `F.toGroupoids` is a Deligne-Mumford stack. -/
@[stacks 03YS]
#check @AlgebraicGeometry.DeligneMumfordStack.ofAlgebraicSpace

/- Lemma 94.13.1 (3): if `X` is an object of `(Sch/S)_fppf`, then
`GroupoidsOver.slice X` is a Deligne-Mumford stack. -/
@[stacks 03YS]
#check @AlgebraicGeometry.DeligneMumfordStack.slice
