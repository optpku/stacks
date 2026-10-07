module

public import stacks_project.Chap76.Definition_76_3_1_Radicial
import StacksCheckRecall

/- Definition 76.3.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. We say `f` is radicial if for any morphism
`Spec(K) ⟶ Y` where `K` is a field the reduction `(Spec(K) ×_Y X)_red` is either
empty or representable by the spectrum of a purely inseparable field extension of
`K`. -/
@[stacks 0481]
#check AlgebraicGeometry.AlgebraicSpace.Radicial
