module

public import stacks_project.Chap62.Definition_62_6_1_Specialization
import StacksCheckRecall

open AlgebraicGeometry

/- Definition 62.6.1 (1): Let `S` be a locally Noetherian scheme. Let `f : X ⟶ S` be a
morphism of schemes which is locally of finite type. Let `r ≥ 0` be an integer. A
relative `r`-cycle on `X / S` is a family `α` of `r`-cycles on fibres of `X / S` such
that for every morphism `g : S' ⟶ S` where `S'` is the spectrum of a discrete
valuation ring we have `sp_{X'/S'}(α_η) = α_0`, where `sp_{X'/S'}` is specialization
of cycles over a DVR and `α_η` (resp. `α_0`) is the value of the base change `g^*α`
at the generic (resp. closed) point of `S'`. -/
@[stacks 0H50]
#check RelativeCycle.IsRelative

/- Definition 62.6.1 (2): the group of all relative `r`-cycles on `X / S` is denoted
`z(X/S, r)`. -/
@[stacks 0H50]
#check RelativeCycle.group
