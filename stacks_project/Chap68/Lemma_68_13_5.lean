module

public import stacks_project.Chap68.Lemma_68_13_12_ResidualSpace

/-!
# Existence and uniqueness of residual spaces at a point

Every point of an algebraic space has a residual-space monomorphism, unique as
a subobject: any two such monomorphisms are related by a unique isomorphism
over the ambient space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsResidualSpace

/-- Lemma 68.13.5 (1): Let `S` be a scheme. Let `X` be an algebraic space over
`S`. Let `x ∈ |X|`. There exists a monomorphism `ι : Z ⟶ X` of algebraic
spaces over `S` such that `Z` satisfies the equivalent conditions of
Lemma 68.13.3 (reduced, locally Noetherian, and a singleton) and the image of
`Points.map ι` is `{x}`. -/
@[stacks 06QZ]
theorem exists_at {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) :
    ∃ (Z : AlgebraicSpace S) (ι : Z ⟶ X), IsResidualSpace ι x :=
  sorry

/-- Lemma 68.13.5 (2): The monomorphism of Lemma 68.13.5 is unique as a
subobject: any two monomorphisms `Z ⟶ X` and `Z' ⟶ X` from algebraic spaces
satisfying the equivalent conditions of Lemma 68.13.3 whose images on points
are `{x}` are related by a unique isomorphism over `X`. -/
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

end IsResidualSpace

end AlgebraicGeometry.AlgebraicSpace
