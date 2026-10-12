/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.FormalFiber.PRing
public import ReasLib.RingTheory.Gorenstein.Ring
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Localization
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.FiniteCoextension
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.FlatExtension

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/-- A dualizing complex over a Noetherian local commutative ring forces all formal fibers of
the ring to be Gorenstein. -/
theorem formalFibersGorenstein
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex H) :
    FieldAlgebraProperty.HoldsOnFormalFibers
      (fun _ R ↦ IsGorensteinRing R) A := sorry

end CategoryTheory.DerivedCategory.IsDualizingComplex
