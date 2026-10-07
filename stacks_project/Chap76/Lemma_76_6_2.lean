module

public import stacks_project.Chap76.Lemma_76_6_2_Comparison
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

/- Lemma 76.6.2: Let `S` be a scheme. Let `i : Z ⟶ X` be an immersion of
algebraic spaces over `S`. Let `φ : U ⟶ X` be an étale morphism where `U` is a
scheme. Set `Z_U = U ×_X Z`, which is a locally closed subscheme of `U`. Then
`C_{Z/X,*}|_{Z_U} = C_{Z_U/U,*}` canonically and functorially in `U`. The
identification is the isomorphism `ConormalAlgebra.restrictEtale` of
quasi-coherent `𝒪_{Z_U}`-algebras, with `Z_U` realised as `pullback i φ` and
restriction as `QcAlgebraUnder.pullback` along `Hom.Conormal.toZ`. -/
@[stacks 09RR]
#check AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.restrictEtale
