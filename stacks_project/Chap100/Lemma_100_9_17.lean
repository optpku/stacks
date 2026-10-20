/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Representable.OpenCover

/-!
# Zariski-locality of representability by schemes

An algebraic stack that is a union of open substacks each equivalent to a
scheme is itself a scheme, i.e. representable as a category fibred in
groupoids over `Over S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u v

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 100.9.17: Let `X` be an algebraic stack covered by a set-indexed
family of open substacks, each representable by a scheme. Then `X` is
representable by a scheme. -/
@[stacks 05WF] #check
  (AlgebraicGeometry.AlgebraicStack.isRepresentable_of_iUnion_openSubstack :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {I : Type v}
    (Y : I → GroupoidsOver S) [∀ i, AlgebraicStack (Y i)]
    (ι : ∀ i, Y i ⟶ X)
    (h_open : ∀ i, Groupoids.Hom.OpenImmersion (ι i))
    (h_cover : ∀ x : Points X, ∃ i, x ∈ Set.range (Points.map (ι i)))
    (h_scheme : ∀ i, FiberedCategoryOver.Groupoids.IsRepresentable (Y i)),
    FiberedCategoryOver.Groupoids.IsRepresentable X)

end AlgebraicGeometry.AlgebraicStack
