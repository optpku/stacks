/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_18_14_Descent
import StacksCheckRecall

/-!
# Lemma 66.18.14

A sheaf on the small étale site of an algebraic space is equivalent to a sheaf
on a presenting atlas equipped with a cocycle isomorphism along the kernel pair.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 66.18.14 (1): for a sheaf F on X_étale, the inverse image
G = φ^{-1} F along a presenting atlas carries a canonical isomorphism
α : t^{-1} G ≅ s^{-1} G. -/
@[stacks 05YY] #check
  (presentationInverseImageIso :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X),
      ∀ F : Sheaf (smallEtaleTopology X) (Type (u + 1)),
        (smallEtaleMorphismOfTopoi (relationT φ)).inverseImage.obj
            (presentationInverseImage φ F) ≅
          (smallEtaleMorphismOfTopoi (relationS φ)).inverseImage.obj
            (presentationInverseImage φ F))


/- Lemma 66.18.14 (2): the functor F ↦ (G, α) is an equivalence between sheaves
on X_étale and pairs (G, α) as above. -/
@[stacks 05YY] #check
  (sheafToPresentationDescent_isEquivalence :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X)
      [Etale φ],
      Function.Surjective (Points.map φ) →
        (sheafToPresentationDescent φ).IsEquivalence)
