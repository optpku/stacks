module

import StacksCheckRecall
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap103.Definition_103_7_1_Comparison

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver

universe u

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
variable {x x' : X.total} (φ : x ⟶ x') (F : etaleModules X)

/- 103.7.0.1 For an algebraic stack `X` and `F` in `Mod(X_étale, 𝒪_X)`, a
morphism `φ : x ⟶ x'` of `X` lying over `f : U ⟶ U'` induces the comparison
morphism `etaleModuleComparison φ F : f_small^*(F|_{U'_étale}) ⟶ F|_{U_étale}`
of `𝒪_{U_étale}`-modules. -/
@[stacks 0761]
#check (etaleModuleComparison φ F :
    ((Scheme.Etale.Small.ringedHom (X.p.map φ).left).modulePullback.{u}).obj
      (restrictEtale F x') ⟶
    restrictEtale F x)
