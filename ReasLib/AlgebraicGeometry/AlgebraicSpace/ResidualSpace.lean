module

public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced

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

/-- Every point of an algebraic space admits a residual-space monomorphism. -/
@[stacks 06QZ]
theorem exists_at {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) :
    ∃ (Z : AlgebraicSpace S) (ι : Z ⟶ X), IsResidualSpace ι x :=
  sorry

/-- Two residual spaces at the same point are related by a unique isomorphism
over the ambient algebraic space. -/
@[stacks 06QZ]
theorem existsUnique_iso {S : Scheme.{u}} {X Z Z' : AlgebraicSpace S}
    {x : Points X} (ι : Z ⟶ X) (ι' : Z' ⟶ X) [IsResidualSpace ι x]
    [IsResidualSpace ι' x] :
    ∃! e : Z ≅ Z', e.hom ≫ ι' = ι :=
  sorry

/-- There is a unique morphism over `X` between residual spaces at the same
point. -/
theorem existsUnique_hom {S : Scheme.{u}} {X Z Z' : AlgebraicSpace S}
    {x : Points X} (ι : Z ⟶ X) (ι' : Z' ⟶ X) [IsResidualSpace ι x]
    [IsResidualSpace ι' x] :
    ∃! g : Z ⟶ Z', g ≫ ι' = ι :=
  sorry

/-- Any morphism over `X` between residual spaces at the same point is an
isomorphism. -/
theorem isIso_of_comp_eq {S : Scheme.{u}} {X Z Z' : AlgebraicSpace S}
    {x : Points X} (ι : Z ⟶ X) (ι' : Z' ⟶ X) [IsResidualSpace ι x]
    [IsResidualSpace ι' x] (g : Z ⟶ Z') (hg : g ≫ ι' = ι) :
    IsIso g :=
  sorry

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

/-- Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `x ∈ |X|` with residual space `Z ⊂ X`. Assume `X` is locally Noetherian.
Then `x` is a closed point of `|X|` if and only if the morphism `Z ⟶ X` is a
closed immersion. -/
@[stacks 0H1U]
theorem mem_closedPoints_iff_isClosedImmersion {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} [IsLocallyNoetherian X] {x : Points X}
    (ι : Z ⟶ X) [IsResidualSpace ι x] :
    x ∈ closedPoints (Points X) ↔ IsClosedImmersion ι :=
  sorry

/-- If a residual-space monomorphism is a closed immersion, then the marked point
is a closed point of `|X|`. -/
theorem mem_closedPoints {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    {x : Points X} (ι : Z ⟶ X) [IsResidualSpace ι x] [IsClosedImmersion ι] :
    x ∈ closedPoints (Points X) :=
  sorry

/-- On a locally Noetherian algebraic space, the residual-space monomorphism of a
closed point is a closed immersion. -/
theorem isClosedImmersion_of_mem_closedPoints {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} [IsLocallyNoetherian X] {x : Points X}
    (ι : Z ⟶ X) [IsResidualSpace ι x] (hx : x ∈ closedPoints (Points X)) :
    IsClosedImmersion ι :=
  sorry

/-- A morphism from a reduced algebraic space to a locally Noetherian algebraic
space whose image on points is contained in `{x}` factors through a residual
space at `x`. -/
@[stacks 0H1S]
theorem exists_lift_of_isLocallyNoetherian {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} [IsReduced Y] [IsLocallyNoetherian X]
    {x : Points X} (ι : Z ⟶ X) [IsResidualSpace ι x] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}) :
    ∃ g : Y ⟶ Z, g ≫ ι = f :=
  sorry

/-- A morphism from a reduced algebraic space to a locally Noetherian algebraic
space whose image on points is contained in `{x}` factors uniquely through a
residual space at `x`. -/
theorem existsUnique_lift_of_isLocallyNoetherian {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} [IsReduced Y] [IsLocallyNoetherian X]
    {x : Points X} (ι : Z ⟶ X) [IsResidualSpace ι x] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}) :
    ∃! g : Y ⟶ Z, g ≫ ι = f :=
  sorry

/-- A morphism from a reduced algebraic space into a locally Noetherian algebraic
space factors through a residual space at `x` if and only if its image on points
is contained in `{x}`. -/
theorem exists_lift_iff_of_isLocallyNoetherian {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} [IsReduced Y] [IsLocallyNoetherian X]
    {x : Points X} (ι : Z ⟶ X) [IsResidualSpace ι x] (f : Y ⟶ X) :
    (∃ g : Y ⟶ Z, g ≫ ι = f) ↔ Set.range (Points.map f) ⊆ {x} :=
  sorry

end IsResidualSpace

end AlgebraicGeometry.AlgebraicSpace
