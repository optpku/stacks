/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.NoNonconstantMorphism
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom

namespace AlgebraicGeometry.ProjectiveSpace

/- Exercise 111.39.4: there is no nonconstant morphism of schemes
`schemeOver ℂ 2 ⟶ schemeOver ℂ 1` over `Spec ℂ`. A constant morphism is one
whose set-theoretic image is a single point. -/
@[stacks 02AA] #check
  (AlgebraicGeometry.ProjectiveSpace.not_exists_isNonconstant :
    ¬ ∃ f : schemeOver ℂ 2 ⟶ schemeOver ℂ 1, f.left.IsNonconstant)

#check
  (AlgebraicGeometry.ProjectiveSpace.range_eq_singleton :
    ∀ f : schemeOver ℂ 2 ⟶ schemeOver ℂ 1,
      ∃ y : scheme ℂ 1, Set.range f.left = {y})

end AlgebraicGeometry.ProjectiveSpace
