module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PropertyBeta
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reasonable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.VeryReasonable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme

/-!
# Inheritance of conditions along representable morphisms

The source of a representable morphism of algebraic spaces inherits property (β),
decency, reasonableness, very reasonableness, and being a scheme from its target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The source of a representable morphism of algebraic spaces over a scheme has
property (β) if its target has property (β). -/
theorem HasPropertyBeta.of_relativelyRepresentable {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f)
    [HasPropertyBeta Y] : HasPropertyBeta X := sorry

/-- The source of a representable morphism of algebraic spaces over a scheme is
decent if its target is decent. -/
theorem IsDecent.of_relativelyRepresentable {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f)
    [IsDecent Y] : IsDecent X := sorry

/-- The source of a representable morphism of algebraic spaces over a scheme is
reasonable if its target is reasonable. -/
theorem IsReasonable.of_relativelyRepresentable {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f)
    [IsReasonable Y] : IsReasonable X := sorry

/-- The source of a representable morphism of algebraic spaces over a scheme is
very reasonable if its target is very reasonable. -/
theorem IsVeryReasonable.of_relativelyRepresentable {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f)
    [IsVeryReasonable Y] : IsVeryReasonable X := sorry

/-- The source of a representable morphism of algebraic spaces over a scheme is
a scheme if its target is a scheme. -/
theorem IsScheme.of_relativelyRepresentable {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f)
    [IsScheme Y] : IsScheme X := sorry

end AlgebraicGeometry.AlgebraicSpace
