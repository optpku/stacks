/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension.BaseChange

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct Algebra.TensorProduct.Right

universe u

namespace CategoryTheory.ModuleCat

/- Compatibility surface for direct Chapter 47 consumers. -/
#check (trivialDualityBaseChangeMap :
  ∀ {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] (K : DerivedCategory (ModuleCat R))
    (h : Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R R')),
    (derivedExtensionOfScalars (algebraMap A (R' ⊗[R] A))).obj
        ((derivedCoextensionOfScalars (algebraMap R A)).obj K) ⟶
      (derivedCoextensionOfScalars (algebraMap R' (R' ⊗[R] A))).obj
        ((derivedExtensionOfScalars (algebraMap R R')).obj K))

#check (trivialDualityBaseChangeMap_adjunct :
  ∀ {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] (K : DerivedCategory (ModuleCat R))
    (h : Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R R')),
    Pushout.DerivedExtension.TensorProduct.comparisonApp
          ((derivedCoextensionOfScalars (algebraMap R A)).obj K) ≫
        (derivedRestrictionCoextensionHomEquiv
          (algebraMap R' (R' ⊗[R] A))
          ((derivedExtensionOfScalars (algebraMap A (R' ⊗[R] A))).obj
            ((derivedCoextensionOfScalars (algebraMap R A)).obj K))
          ((derivedExtensionOfScalars (algebraMap R R')).obj K)).symm
          (trivialDualityBaseChangeMap K h) =
      (derivedExtensionOfScalars (algebraMap R R')).map
        ((derivedRestrictionCoextensionAdjunction (algebraMap R A)).counit.app K))

end CategoryTheory.ModuleCat
