module

public import stacks_project.Chap61.Lemma_61_7_7_Category
public import stacks_project.Chap61.Lemma_61_7_7_Lift
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 61.7.7 (1): Let A be a ring and let I ⊆ A be an ideal. The base change
functor from ind-étale A-algebras to ind-étale A ⧸ I-algebras sending C to
C / I C has a fully faithful right adjoint. -/
@[stacks 097P] #check (CommAlgCat.IndEtale.lift_isFullyFaithfulRightAdjoint :
  ∀ {A : Type u} [CommRing A] (I : Ideal A),
    Nonempty (CommAlgCat.IndEtale.reduction I ⊣ CommAlgCat.IndEtale.lift I) ∧
      Nonempty (CommAlgCat.IndEtale.lift I).FullyFaithful)

/- Lemma 61.7.7 (2): In particular, given an ind-étale A ⧸ I-algebra Ĉ there is
an ind-étale A-algebra C = v(Ĉ) such that Ĉ is isomorphic to C / I C. -/
@[stacks 097P] #check (CommAlgCat.IndEtale.lift_reduction_iso :
  ∀ {A : Type u} [CommRing A] (I : Ideal A)
    (Cbar : CommAlgCat.IndEtale.{u} (A ⧸ I)),
    IsIso (CommAlgCat.IndEtale.counitApp I Cbar))
