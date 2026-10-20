module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.ResidueField
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 47.15.12: derived coextension of a dualizing complex to a maximal-ideal
quotient is a shift of the quotient ring in the derived category. -/
@[stacks 0A7L] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.coextensionToResidueField :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))],
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))) →
    (ω : DerivedCategory (ModuleCat.{u} A)) →
    ω.IsDualizingComplex H →
    (m : Ideal A) → m.IsMaximal →
    ∃ n : ℤ, Nonempty
      ((ModuleCat.derivedCoextensionOfScalars (Ideal.Quotient.mk m)).obj ω ≅
        (shiftFunctor (DerivedCategory (ModuleCat.{u} (A ⧸ m))) n).obj
          (ModuleCat.single0 (ModuleCat.of (A ⧸ m) (A ⧸ m)))))
