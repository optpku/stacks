/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support

/-!
# Factorization through open immersions of algebraic spaces

A morphism of algebraic spaces factors through an open immersion if and only if the
induced map on points lands in the image of that immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsOpenImmersion

/-- A morphism of algebraic spaces factors through an open immersion if and only if the
induced map on points lands in the image of that immersion. -/
theorem exists_lift_iff_range_subset {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsOpenImmersion i] (f : Y ⟶ X) :
    (∃ g : Y ⟶ Z, g ≫ i = f) ↔
      Set.range (Points.map f) ⊆ Set.range (Points.map i) :=
  sorry

/-- A morphism of algebraic spaces factors uniquely through an open immersion if and only if
its image on points is contained in the image of that immersion. -/
theorem existsUnique_lift_iff_range_subset {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsOpenImmersion i] (f : Y ⟶ X) :
    (∃! g : Y ⟶ Z, g ≫ i = f) ↔
      Set.range (Points.map f) ⊆ Set.range (Points.map i) := by
  refine Iff.trans ?_ (exists_lift_iff_range_subset i f)
  sorry

end IsOpenImmersion

namespace OpenSubspace

/-- A morphism of algebraic spaces factors through an open subspace if and only if the image of
points is contained in that subspace. -/
theorem exists_lift_iff_range_subset {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (X' : OpenSubspace X) (f : Y ⟶ X) :
    (∃ g : Y ⟶ X'.X, g ≫ X'.ι = f) ↔ Set.range (Points.map f) ⊆ X'.pointsSet := by
  refine Iff.trans
    (@IsOpenImmersion.exists_lift_iff_range_subset S X Y X'.X X'.ι X'.isOpenImmersion f) ?_
  sorry

end OpenSubspace

end AlgebraicGeometry.AlgebraicSpace
