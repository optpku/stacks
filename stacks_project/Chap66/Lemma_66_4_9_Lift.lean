/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_8_Opens

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

/-- The range criterion for factorization through an open immersion of algebraic spaces, with
uniqueness exposed. Uniqueness follows because an open immersion is a monomorphism. -/
theorem existsUnique_lift_iff_range_subset {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsOpenImmersion i] (f : Y ⟶ X) :
    (∃! g : Y ⟶ Z, g ≫ i = f) ↔
      Set.range (Points.map f) ⊆ Set.range (Points.map i) :=
  sorry

end IsOpenImmersion

namespace OpenSubspace

/-- A morphism of algebraic spaces factors through an open subspace if and only if the image of
points is contained in that subspace. -/
theorem exists_lift_iff_range_subset {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (X' : OpenSubspace X) (f : Y ⟶ X) :
    (∃ g : Y ⟶ X'.X, g ≫ X'.ι = f) ↔ Set.range (Points.map f) ⊆ X'.pointsSet :=
  sorry

end OpenSubspace

end AlgebraicGeometry.AlgebraicSpace
