module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
variable (f : A →+* B) (g : B →+* C)

/- Lemma 47.13.2: Iterated derived coextension along `f : A →+* B` and
`g : B →+* C` is canonically isomorphic to derived coextension along `g.comp f`. -/
@[stacks 0C0F] #check
  (CategoryTheory.ModuleCat.DerivedCoextension.compIso f g :
    CategoryTheory.ModuleCat.derivedCoextensionOfScalars f ⋙
        CategoryTheory.ModuleCat.derivedCoextensionOfScalars g ≅
      CategoryTheory.ModuleCat.derivedCoextensionOfScalars (g.comp f))
