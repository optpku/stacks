module

public import stacks_project.Chap90.«90_7_12_1_Yoneda»
import StacksCheckRecall

/-!
# Evaluation of morphisms from restricted coyoneda

The named equation of Stacks Tag 06SK: morphisms over `C_Λ` from
`underline R |_{C_Λ}` to a category cofibered in groupoids `F` evaluate on
identity truncations to objects of the completion fibre `hat F(R)`.
-/

@[expose] public section

open CategoryTheory

/- 90.7.12.1: if `R` is an object of `Ĉ_Λ` and `p : F ⥤ ArtinianLocalAlgCat Λ k`
is cofibered in groupoids, evaluation of a based morphism
`φ : restrictedCoyoneda R ⟶ p` over `C_Λ` on the identity truncations
`R ⟶ R ⧸ m_R^{n+1}` yields `FormalObject.fromRestrictedHom p R`, a functor
`RestrictedHom p R ⥤ Functor.Fiber (Functor.completion p) R` from
`Mor_{C_Λ}(underline R |_{C_Λ}, F)` to `hat F(R)`, and this functor is an
equivalence of categories. -/
@[stacks 06SK]
#check FormalObject.fromRestrictedHom
