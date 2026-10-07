module

public import stacks_project.Chap65.Lemma_65_15_1_InverseImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits
open scoped MorphismOfTopoiIn

universe u v uC uD

/- The morphisms of topoi `f` and `g` of Topologies Lemma 34.12.2, in the slice
form used for a change of big site over an object `S`. -/
#check CategoryTheory.Functor.Retraction.overCompInverseImageIso

/- Lemma 65.15.1 (1): suppose given big sites `Sch_fppf` and `Sch'_fppf` with
`Sch_fppf` contained in `Sch'_fppf`, and let `S` be an object of `Sch_fppf`.
Let `f, g` be the morphisms of topoi of Topologies Lemma 34.12.2. If a sheaf `F`
on `(Sch/S)_fppf` is representable by a scheme `X` over `S`, then `f⁻¹ F` is
representable by the same scheme `X`, now viewed as an object of `(Sch'/S)_fppf`. -/
@[stacks 03FP] #check AlgebraicGeometry.AlgebraicSpace.inverseImageYonedaIso

/- Lemma 65.15.1 (2): in the same setup, if `F` is an algebraic space over `S`,
then `f⁻¹ F` is an algebraic space over `S`. -/
@[stacks 03FP] #check AlgebraicGeometry.AlgebraicSpace.ofInverseImage
