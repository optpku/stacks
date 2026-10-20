/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Factorization
import StacksCheckRecall

/-!
# Factorization through closed subspaces of algebraic spaces

A morphism from a reduced algebraic space factors through a closed immersion if and
only if the induced map on points lands in the image of that immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.12.4: let `S` be a scheme, let `X` and `Y` be algebraic spaces over `S`,
and let `Z ⊂ X` be a closed subspace, realized as a closed immersion `i : Z ⟶ X`.
Assume `Y` is reduced. A morphism `f : Y ⟶ X` factors through `Z` if and only if
`f(|Y|) ⊆ |Z|`, i.e. `Set.range (Points.map f) ⊆ Set.range (Points.map i)`. -/
@[stacks 03JJ] #check
  (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.exists_lift_iff_range_subset :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} [IsReduced Y]
      (i : Z ⟶ X) [IsClosedImmersion i] (f : Y ⟶ X),
    (∃ g : Y ⟶ Z, g ≫ i = f) ↔
      Set.range (Points.map f) ⊆ Set.range (Points.map i))

/- The range criterion for factorization through a closed immersion of algebraic spaces, with
uniqueness exposed. Uniqueness follows because a closed immersion is a monomorphism. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.existsUnique_lift_iff_range_subset :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} [IsReduced Y]
      (i : Z ⟶ X) [IsClosedImmersion i] (f : Y ⟶ X),
    (∃! g : Y ⟶ Z, g ≫ i = f) ↔
      Set.range (Points.map f) ⊆ Set.range (Points.map i))

/- A morphism from a reduced algebraic space factors through a closed subspace if and only if
the image of points is contained in that subspace. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.exists_lift_iff_range_subset :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (Z : ClosedSubspace X)
      [IsReduced Y] (f : Y ⟶ X),
    (∃ g : Y ⟶ Z.X, g ≫ Z.ι = f) ↔
      Set.range (Points.map f) ⊆ Set.range (Points.map Z.ι))

end AlgebraicGeometry.AlgebraicSpace
