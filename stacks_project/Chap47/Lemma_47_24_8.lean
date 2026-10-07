module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.Finite

@[expose] public section

open CategoryTheory
noncomputable section

universe u

variable {R A : Type u} [CommRing R] [CommRing A]

/- Lemma 47.24.8: for a finite map `φ : R →+* A` of Noetherian rings, upper shriek
along `φ` is naturally isomorphic to derived coextension of scalars `RHom_R(A, -)`. -/
@[stacks 0C0G] #check
  (CategoryTheory.ModuleCat.UpperShriek.Presentation.isomorphicDerivedCoextensionOfFinite :
    ∀ [IsNoetherianRing R] [IsNoetherianRing A]
      (φ : R →+* A), φ.Finite →
      ∀ (p : CategoryTheory.ModuleCat.UpperShriek.Presentation φ),
        IsIsomorphic p.functor (ModuleCat.derivedCoextensionOfScalars φ))

#check
  (CategoryTheory.ModuleCat.UpperShriek.Presentation.objIsomorphicDerivedCoextensionOfFinite :
    ∀ [IsNoetherianRing R] [IsNoetherianRing A]
      (φ : R →+* A), φ.Finite →
      ∀ (p : CategoryTheory.ModuleCat.UpperShriek.Presentation φ)
        (K : DerivedCategory (ModuleCat R)),
        IsIsomorphic (p.functor.obj K) ((ModuleCat.derivedCoextensionOfScalars φ).obj K))
