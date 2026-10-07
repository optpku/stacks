module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap68.Lemma_68_13_12_ResidualSpace

/-!
# Factorization through residual spaces of locally Noetherian algebraic spaces

A morphism from a reduced algebraic space whose image on points is a singleton
`{x}` factors through a residual space at `x` when the target is locally
Noetherian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsResidualSpace

/-- Lemma 68.13.9: Let `S` be a scheme. Let `f : Y ⟶ X` be a morphism of
algebraic spaces over `S`. Let `x ∈ |X|` be a point. Assume `|f|(|Y|)` is
contained in `{x} ⊂ |X|`, `Y` is reduced, and `X` is locally Noetherian.
Then `f` factors through the residual space `Z_x` of `X` at `x`. -/
@[stacks 0H1S]
theorem exists_lift_of_isLocallyNoetherian {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} [IsReduced Y] [IsLocallyNoetherian X]
    {x : Points X} (ι : Z ⟶ X) [IsResidualSpace ι x] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}) :
    ∃ g : Y ⟶ Z, g ≫ ι = f :=
  sorry

/-- A residual-space factorization of a morphism from a reduced algebraic space
into a locally Noetherian algebraic space, supported at a single point, is
unique, because a residual-space morphism is a monomorphism. -/
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
