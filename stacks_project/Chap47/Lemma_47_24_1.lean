module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.Independence

@[expose] public section

open CategoryTheory

universe u

/- Lemma 47.24.1: the upper-shriek functors associated to any two finite polynomial
presentations of a finite-type homomorphism of Noetherian rings are naturally isomorphic. -/
@[stacks 0BZJ] #check
  (CategoryTheory.ModuleCat.UpperShriek.Presentation.functor_isIsomorphic :
    ∀ {R A : Type u} [CommRing R] [CommRing A]
      [IsNoetherianRing R] [IsNoetherianRing A]
      (f : R →+* A) (hf : f.FiniteType)
      (p q : CategoryTheory.ModuleCat.UpperShriek.Presentation f),
      IsIsomorphic p.functor q.functor)
