/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Functor
import StacksCheckRecall

open CategoryTheory

universe u

variable {A : Type u} [CommRing A]
variable (I : Ideal A) (hI : I.FG)

/- 47.9.0.1: for the closed subset `Z = V(I)` associated to the finitely generated ideal
`I`, the intended local-cohomology functor has signature
`D(A) ⟶ D_{I^∞-torsion}(A)`. -/
@[stacks 0A6Q] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.functor I :
    DerivedCategory (ModuleCat A) ⥤
      DerivedCategory.CohomologyIn (ModuleCat.isIdealPowerTorsion I))
