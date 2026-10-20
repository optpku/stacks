module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.OpenImmersion

@[expose] public section

universe u

/- Lemma 47.24.9: if `R` is Noetherian and `φ : R →+* R'` induces an open
immersion `Spec R' ⟶ Spec R`, then upper shriek along `φ` is naturally isomorphic
to derived extension of scalars along `φ`. -/
@[stacks 0C0H] #check
  (CategoryTheory.ModuleCat.UpperShriek.Presentation.isomorphicDerivedExtensionOfIsOpenImmersion :
    ∀ {R R' : Type u} [CommRing R] [CommRing R'] [IsNoetherianRing R]
      (φ : R →+* R')
      (p : CategoryTheory.ModuleCat.UpperShriek.Presentation φ)
      [AlgebraicGeometry.IsOpenImmersion
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ))],
      CategoryTheory.IsIsomorphic p.functor
        (CategoryTheory.ModuleCat.derivedExtensionOfScalars φ))

/- The principal-localization specialization of the open-immersion comparison. -/
#check
  (CategoryTheory.ModuleCat.UpperShriek.Presentation.isomorphicDerivedExtensionOfLocalizationAway :
    ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
      (f : R)
      (p : CategoryTheory.ModuleCat.UpperShriek.Presentation
        (algebraMap R (Localization.Away f))),
      CategoryTheory.IsIsomorphic p.functor
        (CategoryTheory.ModuleCat.derivedExtensionOfScalars
          (algebraMap R (Localization.Away f))))
