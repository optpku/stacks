/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ProjectiveSpace.Beilinson.Equivalence

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

/- Lemma 36.20.1 (1): derived tensoring over the Beilinson matrix algebra with the
Beilinson generator is an `A`-linear equivalence of triangulated categories. -/
@[stacks 0BQU] #check
  (AlgebraicGeometry.ProjectiveSpace.Beilinson.tensorFunctor_isEquivalence :
    ∀ (A : Type u) [CommRing A] (n : ℕ),
      (AlgebraicGeometry.ProjectiveSpace.Beilinson.tensorFunctor A n).IsEquivalence)

#check
  (AlgebraicGeometry.ProjectiveSpace.Beilinson.tensorFunctor_linear :
    ∀ (A : Type u) [CommRing A] (n : ℕ),
      (AlgebraicGeometry.ProjectiveSpace.Beilinson.tensorFunctor A n).Linear A)

#check
  (AlgebraicGeometry.ProjectiveSpace.Beilinson.tensorFunctor_isTriangulated :
    ∀ (A : Type u) [CommRing A] (n : ℕ),
      (AlgebraicGeometry.ProjectiveSpace.Beilinson.tensorFunctor A n).IsTriangulatedWith
        (AlgebraicGeometry.ProjectiveSpace.Beilinson.tensorFunctor_commShift A n))

/- Lemma 36.20.1 (2): the equivalence sends the regular matrix-algebra object to the
Beilinson generator. -/
@[stacks 0BQU] #check
  (AlgebraicGeometry.ProjectiveSpace.Beilinson.regularIso :
    ∀ (A : Type u) [CommRing A] (n : ℕ),
      (AlgebraicGeometry.ProjectiveSpace.Beilinson.tensorFunctor A n).obj
          (AlgebraicGeometry.ProjectiveSpace.Beilinson.regularObject A n) ≅
        AlgebraicGeometry.ProjectiveSpace.derivedBeilinsonGenerator A n)
