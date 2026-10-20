/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion

/-!
# Representability on an open cover

An algebraic stack covered by open substacks representable by schemes or
algebraic spaces is itself representable by a scheme or an algebraic space,
respectively.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u v

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic stack is representable by an algebraic space if it admits a
set-indexed family of open immersions whose images cover its points and whose
domains are representable by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpace_of_iUnion_openSubstack
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {I : Type v}
    (Y : I → GroupoidsOver S) [∀ i, AlgebraicStack (Y i)]
    (ι : ∀ i, Y i ⟶ X)
    (h_open : ∀ i, Groupoids.Hom.OpenImmersion (ι i))
    (h_cover : ∀ x : Points X, ∃ i, x ∈ Set.range (Points.map (ι i)))
    (h_space : ∀ i, IsRepresentableByAlgebraicSpace (Y i)) :
    IsRepresentableByAlgebraicSpace X := sorry

/-- An algebraic stack is representable by a scheme if it admits a set-indexed
family of open immersions whose images cover its points and whose domains are
representable by schemes. -/
theorem isRepresentable_of_iUnion_openSubstack
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {I : Type v}
    (Y : I → GroupoidsOver S) [∀ i, AlgebraicStack (Y i)]
    (ι : ∀ i, Y i ⟶ X)
    (h_open : ∀ i, Groupoids.Hom.OpenImmersion (ι i))
    (h_cover : ∀ x : Points X, ∃ i, x ∈ Set.range (Points.map (ι i)))
    (h_scheme : ∀ i, FiberedCategoryOver.Groupoids.IsRepresentable (Y i)) :
    FiberedCategoryOver.Groupoids.IsRepresentable X := sorry

end AlgebraicGeometry.AlgebraicStack
