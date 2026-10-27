/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe.Stratification
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.GerbeStratification

/- Remark 101.29.4: whether every canonical maximal dense gerbe stratification
has a countable well-ordered index is an open question, expressed as a proposition. -/
@[stacks 06RG] #check (AlgebraicGeometry.AlgebraicStack.GerbeStratification.countableIndex :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [QuasiCompact (forget.{u + 1, u, u, u + 1} X)], Prop)

end AlgebraicGeometry.AlgebraicStack.GerbeStratification
