module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.FaithfullyFlat
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Lemma 47.26.1: a complex of modules over a Noetherian commutative ring is dualizing if
its derived extension along a faithfully flat map to another Noetherian ring is dualizing. -/
@[stacks 0E4A] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.of_faithfullyFlat :
    ∀ {A B : Type u} [CommRing A] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} B))]
      (f : A →+* B), f.FaithfullyFlat →
      (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))) →
      (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u} B))) →
      (K : DerivedCategory (ModuleCat.{u} A)) →
      ((ModuleCat.derivedExtensionOfScalars f).obj K).IsDualizingComplex HB →
      K.IsDualizingComplex HA)
