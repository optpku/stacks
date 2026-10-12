/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.RingTheory.RingHom.Quotient
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/-- Derived extension along a flat homomorphism of Noetherian commutative rings carries a
dualizing complex to a dualizing complex when the homomorphism induces a bijection modulo an
ideal whose extension lies in the target Jacobson radical. -/
theorem flatExtension
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} B))]
    (f : A →+* B) (hflat : f.Flat)
    (I : Ideal A) (hquot : Function.Bijective (f.quotientByIdeal I))
    (hIB : I.map f ≤ Ring.jacobson B)
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u} B)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex HA) :
    ((ModuleCat.derivedExtensionOfScalars f).obj ω).IsDualizingComplex HB := sorry

end CategoryTheory.DerivedCategory.IsDualizingComplex
