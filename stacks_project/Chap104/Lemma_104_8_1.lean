/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.DerivedSections.Parasitic
import StacksCheckRecall

/-!
# Lemma 104.8.1

On an algebraic stack, an object of `D(X_fppf)` with parasitic cohomology
sheaves has vanishing derived sections at every flat object.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.Limits

universe u z

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
variable [UnivLE.{u + 1, z}]

/- Lemma 104.8.1: an unbounded derived object with parasitic cohomology
has zero derived sections at every flat object. -/
@[stacks 0H13] #check
  (AlgebraicGeometry.AlgebraicStack.isZero_rGamma_of_parasitic_cohomology X :
    ∀ (K : DerivedCategory (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z})),
      DerivedCategory.cohomologyIn (vanishesOnFlat X) K →
      ∀ {x : X.total}, isFlat X x →
        IsZero ((siteAbelianSectionsDerived (inheritedFppfTopology X) x).obj K))

end AlgebraicGeometry.AlgebraicStack
