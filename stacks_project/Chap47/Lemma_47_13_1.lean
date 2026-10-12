/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension
import StacksCheckRecall

open CategoryTheory

universe u

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

/- Lemma 47.13.1: for a ring homomorphism `f : A →+* B`, the total right-derived
coextension functor `RHom_A(B, -) : D(A) ⥤ D(B)` is right adjoint to derived restriction
of scalars `D(B) ⥤ D(A)`. -/
@[stacks 0A70] #check
  (CategoryTheory.ModuleCat.derivedRestrictionCoextensionAdjunction f :
    CategoryTheory.ModuleCat.derivedRestrictionOfScalars f ⊣
      CategoryTheory.ModuleCat.derivedCoextensionOfScalars f)
