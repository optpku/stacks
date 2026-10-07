module

public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Definition_66_7_2
public import stacks_project.Chap66.Remark_66_7_3_EtaleLocal

/-!
# Factorization through closed subspaces of algebraic spaces

A morphism from a reduced algebraic space factors through a closed immersion if and
only if the induced map on points lands in the image of that immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsClosedImmersion

/-- Lemma 66.12.4: let `S` be a scheme, let `X` and `Y` be algebraic spaces over `S`,
and let `Z ⊂ X` be a closed subspace, realized as a closed immersion `i : Z ⟶ X`.
Assume `Y` is reduced. A morphism `f : Y ⟶ X` factors through `Z` if and only if
`f(|Y|) ⊆ |Z|`, i.e. `Set.range (Points.map f) ⊆ Set.range (Points.map i)`. -/
@[stacks 03JJ]
theorem exists_lift_iff_range_subset {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (h_reduced : hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) Y)
    (i : Z ⟶ X) [IsClosedImmersion i] (f : Y ⟶ X) :
    (∃ g : Y ⟶ Z, g ≫ i = f) ↔
      Set.range (Points.map f) ⊆ Set.range (Points.map i) :=
  sorry

/-- The range criterion for factorization through a closed immersion of algebraic spaces, with
uniqueness exposed. Uniqueness follows because a closed immersion is a monomorphism. -/
theorem existsUnique_lift_iff_range_subset {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (h_reduced : hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) Y)
    (i : Z ⟶ X) [IsClosedImmersion i] (f : Y ⟶ X) :
    (∃! g : Y ⟶ Z, g ≫ i = f) ↔
      Set.range (Points.map f) ⊆ Set.range (Points.map i) :=
  sorry

end IsClosedImmersion

namespace ClosedSubspace

/-- A morphism from a reduced algebraic space factors through a closed subspace if and only if
the image of points is contained in that subspace. -/
theorem exists_lift_iff_range_subset {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (Z : ClosedSubspace X)
    (h_reduced : hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) Y)
    (f : Y ⟶ X) :
    (∃ g : Y ⟶ Z.X, g ≫ Z.ι = f) ↔
      Set.range (Points.map f) ⊆ Set.range (Points.map Z.ι) :=
  sorry

end ClosedSubspace

end AlgebraicGeometry.AlgebraicSpace
