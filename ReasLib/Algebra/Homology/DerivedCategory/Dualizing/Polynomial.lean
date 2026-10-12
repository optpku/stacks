/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Polynomial.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/-- Derived scalar extension along `Polynomial.C : A →+* Polynomial A` sends a dualizing
complex over a Noetherian commutative ring `A` to a dualizing complex over `Polynomial A`. -/
theorem polynomialExtension
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} (Polynomial A)))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u} (Polynomial A))))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex HA) :
    ((ModuleCat.derivedExtensionOfScalars Polynomial.C).obj ω).IsDualizingComplex HB := sorry

end CategoryTheory.DerivedCategory.IsDualizingComplex
