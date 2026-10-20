module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.RegularQuotient
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Pretriangulated

noncomputable section

universe u

/- Lemma 47.16.10: if `f` is a regular element in the maximal ideal of a Noetherian local
ring `A`, then derived coextension to `A ⨸ principalIdeal f` is normalized dualizing and,
after restriction to `D(A)`, is the first object of the distinguished triangle whose second map
is multiplication by `f` on the original normalized dualizing complex. -/
@[stacks 0A7T]
#check
  (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.regularQuotientTriangle :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      (f : IsLocalRing.maximalIdeal A) (hf : IsRegular (f : A))
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [MonoidalCategory
        (DerivedCategory (ModuleCat.{u} (A ⧸ principalIdeal (f : A))))]
      (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (HB : MonoidalClosed
        (DerivedCategory (ModuleCat.{u} (A ⧸ principalIdeal (f : A)))))
      (ωA : DerivedCategory (ModuleCat.{u} A))
      (hωA : ωA.IsNormalizedDualizingComplex HA),
      let q := Ideal.Quotient.mk (principalIdeal (f : A))
      let ωB := (ModuleCat.derivedCoextensionOfScalars q).obj ωA
      ∃ δ : ωA ⟶ ((ModuleCat.derivedRestrictionOfScalars q).obj ωB)⟦(1 : ℤ)⟧,
        ωB.IsNormalizedDualizingComplex HB ∧
          Triangle.mk
              ((ModuleCat.derivedRestrictionCoextensionAdjunction q).counit.app ωA)
              ((f : A) • 𝟙 ωA) δ ∈ distTriang (DerivedCategory (ModuleCat.{u} A)))
