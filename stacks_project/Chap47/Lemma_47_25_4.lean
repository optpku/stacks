module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.CompleteIntersection

@[expose] public section

universe u

/- Lemma 47.25.4 (1): for a local complete-intersection homomorphism `φ : R →+* A`
of Noetherian rings, its presentation-defined relative dualizing complex is invertible in
`D(A)`. -/
@[stacks 0E4B] #check
  (CategoryTheory.ModuleCat.UpperShriek.Presentation.isInvertibleObject_of_isLocalCompleteIntersection :
    ∀ {R A : Type u} [CommRing R] [CommRing A]
      [IsNoetherianRing R] [IsNoetherianRing A]
      (φ : R →+* A) (p : CategoryTheory.ModuleCat.UpperShriek.Presentation φ)
      [φ.IsLocalCompleteIntersection]
      [CategoryTheory.MonoidalCategory
        (DerivedCategory (ModuleCat.{u, u} A))]
      (T : CategoryTheory.DerivedCategory.DerivedTensor.Right.Monoidal.Model
        (C := ModuleCat.{u, u} A)),
      CategoryTheory.MonoidalCategory.isInvertibleObject
        (p.functor.obj (CategoryTheory.ModuleCat.single0 (ModuleCat.of R R))))

/- Lemma 47.25.4 (2): upper shriek along a local complete-intersection homomorphism
`φ : R →+* A` is, on every `K ∈ D(R)`, derived tensor product with the relative
dualizing complex. -/
@[stacks 0E4B] #check
  (CategoryTheory.ModuleCat.UpperShriek.Presentation.objIsomorphicTensorDualOfLocalCompleteIntersection :
    ∀ {R A : Type u} [CommRing R] [CommRing A]
      [IsNoetherianRing R] [IsNoetherianRing A]
      (φ : R →+* A) (p : CategoryTheory.ModuleCat.UpperShriek.Presentation φ)
      [φ.IsLocalCompleteIntersection]
      (K : DerivedCategory (ModuleCat.{u, u} R)),
      CategoryTheory.IsIsomorphic (p.functor.obj K)
        ((CategoryTheory.derivedTensorChangeOfRings φ
          (p.functor.obj (CategoryTheory.ModuleCat.single0 (ModuleCat.of R R)))).obj K))
