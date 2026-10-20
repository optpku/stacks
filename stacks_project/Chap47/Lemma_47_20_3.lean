module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.CohenMacaulayRing
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 47.20.3: a Noetherian commutative ring admitting a finite module whose
degree-zero complex is dualizing is Cohen--Macaulay. -/
@[stacks 0DW5]
#check (CategoryTheory.DerivedCategory.IsDualizingComplex.cohenMacaulayRingOfSingle :
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : ModuleCat.{u} A) [Module.Finite A ω]
    (hω : (ModuleCat.single0 ω).IsDualizingComplex H),
    CohenMacaulayRing A)

end
