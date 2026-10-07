module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.BaseChange

@[expose] public section

open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u

/- The canonical upper-shriek comparison for a flat coefficient extension. -/
#check
  (CategoryTheory.ModuleCat.UpperShriek.Presentation.flatBaseChange :
    ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
      (p : CategoryTheory.ModuleCat.UpperShriek.Presentation (algebraMap R A))
      (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Flat R R'],
      p.functor ⋙
          CategoryTheory.ModuleCat.derivedExtensionOfScalars
            (algebraMap A (A ⊗[R] R')) ⟶
        CategoryTheory.ModuleCat.derivedExtensionOfScalars (algebraMap R R') ⋙
          (p.baseChange R').functor)

/- Lemma 47.24.4: for a finite-type map R → A and a flat map of Noetherian rings
R → R', the canonical upper-shriek base-change morphisms are functorial, and their
components are isomorphisms on bounded-below objects. -/
@[stacks 0BZN] #check
  (CategoryTheory.ModuleCat.UpperShriek.Presentation.flatBaseChange_app_isIso_of_boundedBelow :
    ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [IsNoetherianRing R]
      (p : CategoryTheory.ModuleCat.UpperShriek.Presentation (algebraMap R A))
      (R' : Type u) [CommRing R'] [Algebra R R']
      [IsNoetherianRing R'] [Module.Flat R R']
      (K : DerivedCategory (ModuleCat.{u, u} R)) (_ : ∃ n : ℤ, K.IsGE n),
      IsIso ((p.flatBaseChange R').app K))
