module

public import stacks_project.Chap67.Lemma_67_11_2_Pushforward
import StacksCheckRecall

@[expose] public section

/- Lemma 67.11.2: let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S`. If `f` is quasi-compact and quasi-separated, then `f_*` transforms quasi-coherent
`𝒪_X`-modules into quasi-coherent `𝒪_Y`-modules. -/
@[stacks 03M9]
#check AlgebraicGeometry.AlgebraicSpace.Modules.pushforward.isQuasicoherent

#check AlgebraicGeometry.AlgebraicSpace.QCoh.pushforward
