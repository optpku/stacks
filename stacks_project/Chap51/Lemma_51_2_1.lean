/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Affine
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.DerivedCategory.LocalCohomology

universe u

/- Lemma 51.2.1 -/
@[stacks 0A6T] #check (CategoryTheory.DerivedCategory.LocalCohomology.affineComparison_isomorphic :
  ∀ {A : CommRingCat.{u}} (I : Ideal A) (_ : I.FG),
    ∀ (RΓ : (DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)),
      (IdealPowerTorsion.inclusion I ⊣ RΓ) →
        IsIsomorphic (RΓ ⋙ IdealPowerTorsion.inclusion I)
          (AlgebraicGeometry.Scheme.DerivedQCoh.affineGlobalSectionsWithSupport I))
