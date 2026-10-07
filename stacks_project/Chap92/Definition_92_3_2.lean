module

public import stacks_project.Chap110.Lemma_110_43_1_Cotangent
import StacksCheckRecall

/- Definition 92.3.2: The cotangent complex `L_{B/A}` of a ring map `A ⟶ B` is
the complex of `B`-modules associated to the simplicial `B`-module
`Ω_{P_•/A} ⊗_{P_•, ε} B`, where `ε : P_• ⟶ B` is the standard resolution of `B`
over `A`. -/
@[stacks 08PN]
#check @RingHom.cotangentComplex

#check @Algebra.cotangentComplex
#check @CategoryTheory.CommRingCat.Under.CotangentComplex.obj
#check @CategoryTheory.CommRingCat.Under.CotangentComplex.simplicialModule
#check @CategoryTheory.CommRingCat.Under.CotangentComplex.obj_X
#check @CategoryTheory.CommRingCat.Under.CotangentComplex.isZero_obj_X_of_pos
