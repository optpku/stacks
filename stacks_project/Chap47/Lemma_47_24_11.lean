module

import StacksCheckRecall
import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.Dualizing

@[expose] public section

open CategoryTheory
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace CategoryTheory
namespace ModuleCat
namespace UpperShriek
namespace Presentation

variable {A B : Type u} [CommRing A] [CommRing B]
  [IsNoetherianRing A] [IsNoetherianRing B]
  [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} A))]
  [BraidedCategory (DerivedCategory (ModuleCat.{u, u} A))]
  [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} B))]
  [BraidedCategory (DerivedCategory (ModuleCat.{u, u} B))]

/- Lemma 47.24.11: for a finite-type homomorphism `φ : A →+* B` of Noetherian rings,
upper shriek on `D[ModuleCat.isFG A]` is naturally isomorphic to duality over `B`
applied after duality over `A` and derived extension of scalars. -/
@[stacks 0E9L] #check
  (CategoryTheory.ModuleCat.UpperShriek.Presentation.isomorphicDualityExtension :
    ∀ (φ : A →+* B) (hφ : φ.FiniteType) (p : Presentation φ)
      (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u, u} A)))
      (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u, u} B)))
      (ωA : DerivedCategory (ModuleCat.{u, u} A)) (hωA : ωA.IsDualizingComplex HA),
      IsIsomorphic
        ((DerivedCategory.cohomologyIn (ModuleCat.isFG A)).ι ⋙ p.functor)
        ((DerivedCategory.IsDualizingComplex.coherentDuality HA ωA hωA).rightOp ⋙
          (DerivedCategory.cohomologyIn (ModuleCat.isFG A)).ι.op ⋙
          (derivedExtensionOfScalars φ).op ⋙
          (RightInternalHom.ofBraidedClosedOf HB).dualFunctor (p.functor.obj ωA)))

/- The objectwise form of the functorial comparison. -/
#check
  (CategoryTheory.ModuleCat.UpperShriek.Presentation.objIsomorphicDualityExtension :
    ∀ (φ : A →+* B) (hφ : φ.FiniteType) (p : Presentation φ)
      (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u, u} A)))
      (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u, u} B)))
      (ωA : DerivedCategory (ModuleCat.{u, u} A)) (hωA : ωA.IsDualizingComplex HA)
      (K : D[ModuleCat.isFG A]),
      IsIsomorphic (p.functor.obj K.obj)
        (((DerivedCategory.IsDualizingComplex.coherentDuality HA ωA hωA).rightOp ⋙
          (DerivedCategory.cohomologyIn (ModuleCat.isFG A)).ι.op ⋙
          (derivedExtensionOfScalars φ).op ⋙
          (RightInternalHom.ofBraidedClosedOf HB).dualFunctor (p.functor.obj ωA)).obj K))

end Presentation
end UpperShriek
end ModuleCat
end CategoryTheory
