module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidualSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.FiniteAbove
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent

/-!
# Factorization through residual spaces at quasi-compact field-valued points

A morphism from a reduced algebraic space whose image on points is a singleton
`{x}` factors through a residual space at `x` when `x` is represented by a
quasi-compact monomorphism from the spectrum of a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsResidualSpace

/-- A morphism from a reduced algebraic space whose image on points is contained
in `{x}` factors through any residual space at `x` when `x` is represented by a
quasi-compact monomorphism from the spectrum of a field. -/
@[stacks 0H1T]
theorem exists_lift_of_range_subset_singleton {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} [IsReduced Y] {x : Points X} (ι : Z ⟶ X)
    [IsResidualSpace ι x] (hx : existsQuasiCompactMonoFieldValuedPoint X x)
    (f : Y ⟶ X) (h_image : Set.range (Points.map f) ⊆ {x}) :
    ∃ g : Y ⟶ Z, g ≫ ι = f :=
  sorry

/-- A residual-space factorization of a morphism from a reduced algebraic space
supported at a point represented by a quasi-compact monomorphism `Spec(k) ⟶ X`
is unique, because a residual-space morphism is a monomorphism. -/
theorem existsUnique_lift_of_range_subset_singleton {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} [IsReduced Y] {x : Points X} (ι : Z ⟶ X)
    [IsResidualSpace ι x] (hx : existsQuasiCompactMonoFieldValuedPoint X x)
    (f : Y ⟶ X) (h_image : Set.range (Points.map f) ⊆ {x}) :
    ∃! g : Y ⟶ Z, g ≫ ι = f :=
  sorry

/-- A morphism from a reduced algebraic space factors through a residual space at
`x` if and only if its image on points is contained in `{x}`, provided `x` is
represented by a quasi-compact monomorphism `Spec(k) ⟶ X`. -/
theorem exists_lift_iff_range_subset_singleton {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} [IsReduced Y] {x : Points X} (ι : Z ⟶ X)
    [IsResidualSpace ι x] (hx : existsQuasiCompactMonoFieldValuedPoint X x)
    (f : Y ⟶ X) :
    (∃ g : Y ⟶ Z, g ≫ ι = f) ↔ Set.range (Points.map f) ⊆ {x} :=
  sorry

/-- If `X` is decent, a morphism from a reduced algebraic space whose image on
points is contained in `{x}` factors through any residual space of `X` at `x`. -/
theorem exists_lift_of_isDecent {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    [IsReduced Y] [IsDecent X] {x : Points X} (ι : Z ⟶ X)
    [IsResidualSpace ι x] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}) :
    ∃ g : Y ⟶ Z, g ≫ ι = f :=
  sorry

end IsResidualSpace

namespace FieldValuedPoint

/-- A morphism from a reduced algebraic space whose image on points is contained
in the singleton represented by a quasi-compact monomorphism `p : Spec(k) ⟶ X`
factors through `p.hom`. -/
theorem exists_lift_of_range_subset_singleton {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsReduced Y] (p : FieldValuedPoint X)
    [QuasiCompact p.hom] [Mono p.hom] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {Points.mk p}) :
    ∃ g : Y ⟶ ofOver p.overObj, g ≫ p.hom = f :=
  sorry

end FieldValuedPoint

end AlgebraicGeometry.AlgebraicSpace
