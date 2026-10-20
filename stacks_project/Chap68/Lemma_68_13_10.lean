module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidualSpace.Factorization
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 68.13.10: A morphism of algebraic spaces over a scheme from a reduced
space whose image is contained in `{x}` factors through the residual space at
`x`, provided `x` is represented by a quasi-compact monomorphism from the
spectrum of a field. The field-valued-point check below records factorization
through that specified field spectrum. -/
@[stacks 0H1T]
#check (AlgebraicGeometry.AlgebraicSpace.IsResidualSpace.exists_lift_of_range_subset_singleton :
    ∀ {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} [IsReduced Y] {x : Points X} (ι : Z ⟶ X)
    [IsResidualSpace ι x] (hx : existsQuasiCompactMonoFieldValuedPoint X x)
    (f : Y ⟶ X) (h_image : Set.range (Points.map f) ⊆ {x}),
    ∃ g : Y ⟶ Z, g ≫ ι = f)

#check (AlgebraicGeometry.AlgebraicSpace.IsResidualSpace.existsUnique_lift_of_range_subset_singleton :
    ∀ {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} [IsReduced Y] {x : Points X} (ι : Z ⟶ X)
    [IsResidualSpace ι x] (hx : existsQuasiCompactMonoFieldValuedPoint X x)
    (f : Y ⟶ X) (h_image : Set.range (Points.map f) ⊆ {x}),
    ∃! g : Y ⟶ Z, g ≫ ι = f)

#check (AlgebraicGeometry.AlgebraicSpace.IsResidualSpace.exists_lift_iff_range_subset_singleton :
    ∀ {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} [IsReduced Y] {x : Points X} (ι : Z ⟶ X)
    [IsResidualSpace ι x] (hx : existsQuasiCompactMonoFieldValuedPoint X x)
    (f : Y ⟶ X),
    (∃ g : Y ⟶ Z, g ≫ ι = f) ↔ Set.range (Points.map f) ⊆ {x})

#check (AlgebraicGeometry.AlgebraicSpace.IsResidualSpace.exists_lift_of_isDecent :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    [IsReduced Y] [IsDecent X] {x : Points X} (ι : Z ⟶ X)
    [IsResidualSpace ι x] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}),
    ∃ g : Y ⟶ Z, g ≫ ι = f)

#check (AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint.exists_lift_of_range_subset_singleton :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsReduced Y] (p : FieldValuedPoint X)
    [QuasiCompact p.hom] [Mono p.hom] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {Points.mk p}),
    ∃ g : Y ⟶ ofOver p.overObj, g ≫ p.hom = f)

