/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Pushout.TorIndependent
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct Algebra.TensorProduct.Right

universe u

namespace CategoryTheory.ModuleCat

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']

/-- The base-change morphism for trivial duality. Its source is obtained by first taking
derived coextension along R ⟶ A and then derived extension along A ⟶ R' ⊗[R] A; its target is
obtained in the opposite order. -/
noncomputable def trivialDualityBaseChangeMap
    (K : DerivedCategory (ModuleCat R))
    (h : Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R R')) :
    (derivedExtensionOfScalars (algebraMap A (R' ⊗[R] A))).obj
        ((derivedCoextensionOfScalars (algebraMap R A)).obj K) ⟶
      (derivedCoextensionOfScalars (algebraMap R' (R' ⊗[R] A))).obj
        ((derivedExtensionOfScalars (algebraMap R R')).obj K) :=
  let hIso : IsIso (Pushout.DerivedExtension.TensorProduct.comparisonApp
      (R := R) (A := A) (R' := R')
      ((derivedCoextensionOfScalars (algebraMap R A)).obj K)) :=
    Pushout.DerivedExtension.TensorProduct.comparisonApp_isIso_of_torIndependent
      (R := R) (A := A) (R' := R') ((derivedCoextensionOfScalars (algebraMap R A)).obj K) h
  derivedRestrictionCoextensionHomEquiv
    (algebraMap R' (R' ⊗[R] A))
    ((derivedExtensionOfScalars (algebraMap A (R' ⊗[R] A))).obj
      ((derivedCoextensionOfScalars (algebraMap R A)).obj K))
    ((derivedExtensionOfScalars (algebraMap R R')).obj K)
    (@inv _ _ _ _ (Pushout.DerivedExtension.TensorProduct.comparisonApp
        (R := R) (A := A) (R' := R')
        ((derivedCoextensionOfScalars (algebraMap R A)).obj K)) hIso ≫
      (derivedExtensionOfScalars (algebraMap R R')).map
        ((derivedRestrictionCoextensionAdjunction (algebraMap R A)).counit.app K))

/-- The adjoint of trivialDualityBaseChangeMap is characterized by the scalar-extended
counit after the canonical derived pushout comparison. -/
theorem trivialDualityBaseChangeMap_adjunct
    (K : DerivedCategory (ModuleCat R))
    (h : Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R R')) :
    Pushout.DerivedExtension.TensorProduct.comparisonApp
          ((derivedCoextensionOfScalars (algebraMap R A)).obj K) ≫
        (derivedRestrictionCoextensionHomEquiv
          (algebraMap R' (R' ⊗[R] A))
          ((derivedExtensionOfScalars (algebraMap A (R' ⊗[R] A))).obj
            ((derivedCoextensionOfScalars (algebraMap R A)).obj K))
          ((derivedExtensionOfScalars (algebraMap R R')).obj K)).symm
          (trivialDualityBaseChangeMap K h) =
      (derivedExtensionOfScalars (algebraMap R R')).map
        ((derivedRestrictionCoextensionAdjunction (algebraMap R A)).counit.app K) := sorry

end CategoryTheory.ModuleCat
