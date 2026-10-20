/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Representable.OpenCover
import StacksCheckRecall

/-!
# Zariski-locality of representability by algebraic spaces

An algebraic stack that is a union of open substacks each representable by
an algebraic space is itself representable by an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u v

open AlgebraicGeometry.AlgebraicStack

/- Lemma 100.9.16: An algebraic stack covered by a set-indexed family of
open substacks, each representable by an algebraic space, is representable
by an algebraic space. -/
@[stacks 05WE] #check
  (AlgebraicGeometry.AlgebraicStack.isRepresentableByAlgebraicSpace_of_iUnion_openSubstack :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {I : Type v}
      (Y : I → GroupoidsOver S) [∀ i, AlgebraicStack (Y i)]
      (ι : ∀ i, Y i ⟶ X)
      (h_open : ∀ i, Groupoids.Hom.OpenImmersion (ι i))
      (h_cover : ∀ x : Points X, ∃ i, x ∈ Set.range (Points.map (ι i)))
      (h_space : ∀ i, IsRepresentableByAlgebraicSpace (Y i)),
      IsRepresentableByAlgebraicSpace X)
