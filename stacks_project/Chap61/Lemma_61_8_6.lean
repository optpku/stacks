module

public import stacks_project.Chap61.Lemma_61_5_1_Localization
public import stacks_project.Chap61.Lemma_61_8_4_Retraction
public import ReasLib.RingTheory.Etale.Retraction.Specializing
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 61.8.6: if every faithfully flat étale ring map out of `A` has a
retraction, and `Z ⊂ Spec(A)` is a closed subscheme, then the same retraction
property holds for the specializing localization
`Localization.specializing (1 : A) I` constructed in Lemma 61.5.1, where
`Z = V(I)`. -/
@[stacks 097W] #check
  (Algebra.HasFaithfullyFlatEtaleRetraction.specializing :
    ∀ {A : Type u} [CommRing A]
      [Algebra.HasFaithfullyFlatEtaleRetraction A] (I : Ideal A),
      Algebra.HasFaithfullyFlatEtaleRetraction
        (Localization.specializing (1 : A) I))
