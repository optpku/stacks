/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

#check (derivedRestrictionCoextensionAdjunction f :
  derivedRestrictionOfScalars f ⊣ derivedCoextensionOfScalars f)

end CategoryTheory.ModuleCat
