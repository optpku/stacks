module

public import stacks_project.Chap75.Lemma_75_3_1_Comparison
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_3_1_Restrict
import StacksCheckRecall

@[expose] public section

/- Lemma 75.3.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Given an étale morphism `V ⟶ Y`, set `U = V ×_Y X` and denote
`g : U ⟶ V` the projection morphism. Then `(Rf_* E)|_V ≅ Rg_*(E|_U)` for `E` in
`D(𝒪_X)`. -/
@[stacks 08GE] #check AlgebraicGeometry.AlgebraicSpace.Modules.derivedPushforwardEtaleBaseChangeIso
