/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_5_2_Comparison
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

/- Lemma 76.5.2: Let `S` be a scheme. Let `i : Z ⟶ X` be an immersion. Let
`φ : U ⟶ X` be an étale morphism where `U` is a scheme. Set `Z_U = U ×_X Z`,
which is a locally closed subscheme of `U`. Then `C_{Z/X}|_{Z_U} = C_{Z_U/U}`
canonically and functorially in `U`. The identification is the isomorphism
`Hom.Conormal.restrictEtale` of quasi-coherent `𝒪_{Z_U}`-modules, with
`Z_U` realised as `pullback i φ` and restriction as `Modules.pullback` along
`Hom.Conormal.toZ`. -/
@[stacks 04CO]
#check AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.restrictEtale
