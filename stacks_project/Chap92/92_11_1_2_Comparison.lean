/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.NaiveComparison
public import stacks_project.Chap92.«92_11_1_1_Comparison»

/-!
# Compatibility names for the truncated naive cotangent comparison
-/

@[expose] public section

open CategoryTheory
open CommRingCat.Under.FreeAlgebra
open CommRingCat.Under.CotangentComplex
open DerivedCategory.TStructure

universe u

noncomputable section

namespace Algebra.NaiveCotangent

/-- The truncated comparison from the scalar-extended two-term conormal complex of a
polynomial arrow. -/
abbrev toTruncGE (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    DerivedCategory.Q.obj (naiveComplex A B E φ) ⟶
      (t.truncGE (-1)).obj (DerivedCategory.Q.obj (obj A B)) :=
  naiveCotangentToTruncGE A B E φ

/-- The comparison factors through the truncated evaluation map and the inverse of the
truncated mapping-cone inclusion. -/
theorem toTruncGE_fac (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    toTruncGE A B E φ =
      (t.truncGEπ (-1)).app (DerivedCategory.Q.obj (naiveComplex A B E φ)) ≫
        (t.truncGE (-1)).map (DerivedCategory.Q.map (evaluationToCone A B E φ)) ≫
          (truncGEEvaluationIso A B).hom :=
  naiveCotangentToTruncGE_fac A B E φ

end Algebra.NaiveCotangent
