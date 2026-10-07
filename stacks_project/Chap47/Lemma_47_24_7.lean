module

import StacksCheckRecall
import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.Composition

@[expose] public section

open CategoryTheory
open ModuleCat.UpperShriek
open ModuleCat.UpperShriek.Presentation
open DerivedCategory.TStructure

noncomputable section

universe u

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/- Lemma 47.24.7 - composable finite-type maps of Noetherian rings have an upper-shriek
composition comparison that is an isomorphism on bounded-below derived objects. -/
@[stacks 0BZT] #check (CategoryTheory.ModuleCat.UpperShriek.Presentation.compComparison_isIso_on_boundedBelow :
    ∀ [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      (a : A →+* B) (b : B →+* C) (ha : a.FiniteType) (hb : b.FiniteType)
      (p : Presentation a) (q : Presentation b),
      (t.plus : ObjectProperty (DerivedCategory (ModuleCat A))) ≤
        NatTrans.isomorphismLocus (compComparison p q))

end
