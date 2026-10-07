module

public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Lemma_67_48_6_Reduced

/-!
# Residual spaces of algebraic spaces

A residual space of an algebraic space `X` at a point `x` is a monomorphism
`Z ⟶ X` from a reduced, locally Noetherian singleton algebraic space whose
image on points is `{x}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A monomorphism `ι : Z ⟶ X` of algebraic spaces is a residual space of `X` at
`x` when `Z` is reduced, locally Noetherian, and a singleton, and the image of
`Points.map ι` is `{x}`. -/
class IsResidualSpace {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (ι : Z ⟶ X) (x : Points X) : Prop where
  /-- A residual-space morphism is a monomorphism. -/
  [mono : Mono ι]
  /-- The residual space is reduced. -/
  [isReduced : IsReduced Z]
  /-- The residual space is locally Noetherian. -/
  [isLocallyNoetherian : IsLocallyNoetherian Z]
  /-- The residual space is a singleton. -/
  [subsingleton_points : Subsingleton (Points Z)]
  /-- The image of `Points.map ι` is the singleton `{x}`. -/
  image_eq : Set.range (Points.map ι) = {x}

namespace IsResidualSpace

/-- A residual-space monomorphism is a monomorphism from a reduced, locally
Noetherian singleton algebraic space whose image on points is `{x}`. -/
theorem spec {S : Scheme.{u}} {X Z : AlgebraicSpace S} {ι : Z ⟶ X}
    {x : Points X} [IsResidualSpace ι x] :
    Mono ι ∧ IsReduced Z ∧ IsLocallyNoetherian Z ∧ Subsingleton (Points Z) ∧
      Set.range (Points.map ι) = {x} :=
  sorry

/-- A morphism of algebraic spaces is a residual space at `x` if and only if it
is a monomorphism from a reduced, locally Noetherian singleton whose image on
points is `{x}`. -/
theorem iff {S : Scheme.{u}} {X Z : AlgebraicSpace S} (ι : Z ⟶ X)
    (x : Points X) :
    IsResidualSpace ι x ↔
      Mono ι ∧ IsReduced Z ∧ IsLocallyNoetherian Z ∧ Subsingleton (Points Z) ∧
        Set.range (Points.map ι) = {x} :=
  sorry

/-- The identity of a reduced, locally Noetherian singleton algebraic space is a
residual space at its unique point. -/
instance id {S : Scheme.{u}} {Z : AlgebraicSpace S} [IsReduced Z]
    [IsLocallyNoetherian Z] [Subsingleton (Points Z)] {x : Points Z} :
    IsResidualSpace (𝟙 Z) x :=
  sorry

/-- Every point of a residual space maps to the marked point of the target. -/
theorem map_eq {S : Scheme.{u}} {X Z : AlgebraicSpace S} {ι : Z ⟶ X}
    {x : Points X} [IsResidualSpace ι x] (z : Points Z) :
    Points.map ι z = x :=
  sorry

end IsResidualSpace

end AlgebraicGeometry.AlgebraicSpace
