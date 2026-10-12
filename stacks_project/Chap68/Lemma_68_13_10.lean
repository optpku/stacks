/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap68.Lemma_68_4_5_Fibre
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap68.Lemma_68_13_12_ResidualSpace

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

/-- Lemma 68.13.10: Let `S` be a scheme. Let `f : Y ⟶ X` be a morphism of
algebraic spaces over `S`. Let `x ∈ |X|`. Assume `|f|(|Y|)` is contained in
`{x} ⊂ |X|`, `Y` is reduced, and `x` can be represented by a quasi-compact
monomorphism `Spec(k) ⟶ X` where `k` is a field (for example if `X` is decent).
Then `f` factors through the residual space `Z_x` of `X` at `x`, and
`Z_x = Spec(k)`. -/
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

/-- A morphism from a reduced algebraic space whose image on points is the
singleton of a quasi-compact monomorphism `p : Spec(k) ⟶ X` factors through
`p.hom`, recovering the identification `Z_x = Spec(k)`. -/
theorem exists_lift_of_range_subset_singleton {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsReduced Y] (p : FieldValuedPoint X)
    [QuasiCompact p.hom] [Mono p.hom] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {Points.mk p}) :
    ∃ g : Y ⟶ ofOver p.overObj, g ≫ p.hom = f :=
  sorry

end FieldValuedPoint

end AlgebraicGeometry.AlgebraicSpace
