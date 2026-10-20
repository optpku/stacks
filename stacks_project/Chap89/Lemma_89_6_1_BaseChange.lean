/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.BaseChange.Completion
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints

/-!
# Base change of an algebraic space to the maximal-ideal-adic completion

Typed checks expose the completion base-change construction and its projections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.specAdicCompletionSchemeHom :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A],
    Spec (.of (AdicCompletion (maximalIdeal A) A)) ⟶ Spec (.of A))

#check (AlgebraicGeometry.AlgebraicSpace.specAdicCompletionSchemeHom_eq :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A],
    specAdicCompletionSchemeHom A =
      Spec.map (CommRingCat.ofHom
        (algebraMap A (AdicCompletion (maximalIdeal A) A))))

#check (AlgebraicGeometry.AlgebraicSpace.specAdicCompletion :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A],
    AlgebraicSpace (Spec (.of A)))

#check (AlgebraicGeometry.AlgebraicSpace.specAdicCompletion_eq :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A],
    specAdicCompletion A = ofOver (Over.mk (specAdicCompletionSchemeHom A)))

#check (AlgebraicGeometry.AlgebraicSpace.specAdicCompletionHom :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A],
    specAdicCompletion A ⟶ ofOver (Over.mk (𝟙 (Spec (.of A)))))

#check (AlgebraicGeometry.AlgebraicSpace.specAdicCompletionHom_eq :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A],
    specAdicCompletionHom A =
      ofOverHomMk (specAdicCompletionSchemeHom A)
        (Category.comp_id (specAdicCompletionSchemeHom A)))

#check (AlgebraicGeometry.AlgebraicSpace.completionBaseChange :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A]
    (X : AlgebraicSpace (Spec (.of A))), AlgebraicSpace (Spec (.of A)))

#check (AlgebraicGeometry.AlgebraicSpace.completionBaseChange_eq :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A]
    (X : AlgebraicSpace (Spec (.of A))),
    completionBaseChange A X = pullback (toBase X) (specAdicCompletionHom A))

#check (AlgebraicGeometry.AlgebraicSpace.completionBaseChange.fst :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A]
    (X : AlgebraicSpace (Spec (.of A))), completionBaseChange A X ⟶ X)

#check (AlgebraicGeometry.AlgebraicSpace.completionBaseChange.snd :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A]
    (X : AlgebraicSpace (Spec (.of A))),
    completionBaseChange A X ⟶ specAdicCompletion A)

#check (AlgebraicGeometry.AlgebraicSpace.isPullback_completionBaseChange :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A]
    (X : AlgebraicSpace (Spec (.of A))),
    IsPullback (completionBaseChange.fst A X) (completionBaseChange.snd A X)
      (toBase X) (specAdicCompletionHom A))

end AlgebraicGeometry.AlgebraicSpace
