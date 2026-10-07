module

public import stacks_project.Chap63.Lemma_63_6_1_Module
public import stacks_project.Chap63.Lemma_63_6_1_UpperShriek
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

/- Lemma 63.6.1 (1): Let `f : X ⟶ Y` be a locally quasi-finite morphism of
schemes. The functor `f_! : Ab(X_étale) ⥤ Ab(Y_étale)` has a right adjoint
`f^! : Ab(Y_étale) ⥤ Ab(X_étale)`, as the adjunction
`lowerShriek f ⊣ upperShriek f`. This `f^!` is the non-derived functor. -/
@[stacks 0F59]
#check lowerShriekAdjunction

/- Lemma 63.6.1 (2): for a locally quasi-finite morphism `f : X ⟶ Y` one has
`f^!(ȳ_* A) ≅ ∏_{f(x̄)=ȳ} x̄_* A`, naturally in the abelian group `A`, as the
isomorphism `upperShriekSkyscraperIso`. -/
@[stacks 0F59]
#check upperShriekSkyscraperIso

/- Lemma 63.6.1 (3): if `Λ` is a ring, then
`f_! : Mod(X_étale, Λ) ⥤ Mod(Y_étale, Λ)` has a right adjoint
`f^! : Mod(Y_étale, Λ) ⥤ Mod(X_étale, Λ)`, as the adjunction
`lowerShriekModule f Λ ⊣ upperShriekModule f Λ`. -/
@[stacks 0F59]
#check lowerShriekModuleAdjunction

/- Lemma 63.6.1 (4): the module-valued right adjoint `f^!` agrees with the
abelian `f^!` on underlying abelian sheaves, as the mate isomorphism
`upperShriekModule_forget` along `sheafCompose` of
`forget₂ (ModuleCat Λ) AddCommGrpCat`. -/
@[stacks 0F59]
#check upperShriekModule_forget

end
