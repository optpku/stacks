/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Duality
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Polynomial
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.FiniteCoextension

@[expose] public section

open CategoryTheory
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.UpperShriek.Presentation

variable {R A : Type u} [CommRing R] [CommRing A]
  [IsNoetherianRing R] [IsNoetherianRing A]
  [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} R))]
  [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} A))]

/-- A presentation-defined upper-shriek functor sends a dualizing complex over the source ring to a dualizing complex over the target ring. -/
theorem mapsDualizingComplex
    (f : R →+* A) (hf : f.FiniteType) (p : Presentation f)
    (HR : MonoidalClosed (DerivedCategory (ModuleCat.{u, u} R)))
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u, u} A)))
    (ω : DerivedCategory (ModuleCat.{u, u} R)) (hω : ω.IsDualizingComplex HR) :
    (p.functor.obj ω).IsDualizingComplex HA := sorry

variable {B : Type u} [CommRing B] [IsNoetherianRing B]
  [BraidedCategory (DerivedCategory (ModuleCat.{u, u} A))]
  [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} B))]
  [BraidedCategory (DerivedCategory (ModuleCat.{u, u} B))]

/-- For a finite-type ring homomorphism, presentation-defined upper shriek on coherent
complexes is naturally isomorphic to scalar extension between the corresponding dualities. -/
theorem isomorphicDualityExtension
    (φ : A →+* B) (hφ : φ.FiniteType) (p : Presentation φ)
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u, u} A)))
    (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u, u} B)))
    (ωA : DerivedCategory (ModuleCat.{u, u} A))
    (hωA : ωA.IsDualizingComplex HA) :
    IsIsomorphic
      ((DerivedCategory.cohomologyIn (ModuleCat.isFG A)).ι ⋙ p.functor)
      ((DerivedCategory.IsDualizingComplex.coherentDuality HA ωA hωA).rightOp ⋙
        (DerivedCategory.cohomologyIn (ModuleCat.isFG A)).ι.op ⋙
        (derivedExtensionOfScalars φ).op ⋙
        (RightInternalHom.ofBraidedClosedOf HB).dualFunctor (p.functor.obj ωA)) := sorry

/-- Evaluating the functorial upper-shriek comparison at `K` identifies `φ⁗(K)` with
the dual over `B` of the scalar extension of the dual of `K` over `A`. -/
theorem objIsomorphicDualityExtension
    (φ : A →+* B) (hφ : φ.FiniteType) (p : Presentation φ)
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u, u} A)))
    (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u, u} B)))
    (ωA : DerivedCategory (ModuleCat.{u, u} A))
    (hωA : ωA.IsDualizingComplex HA) (K : D[ModuleCat.isFG A]) :
    IsIsomorphic (p.functor.obj K.obj)
      (((DerivedCategory.IsDualizingComplex.coherentDuality HA ωA hωA).rightOp ⋙
        (DerivedCategory.cohomologyIn (ModuleCat.isFG A)).ι.op ⋙
        (derivedExtensionOfScalars φ).op ⋙
        (RightInternalHom.ofBraidedClosedOf HB).dualFunctor (p.functor.obj ωA)).obj K) := sorry

end CategoryTheory.ModuleCat.UpperShriek.Presentation
