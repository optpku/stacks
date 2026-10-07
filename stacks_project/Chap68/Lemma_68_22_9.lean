module

public import stacks_project.Chap68.Lemma_68_22_7_Map
public import stacks_project.Chap67.Definition_67_45_2_Integral

/-!
# Factorization of integral birational morphisms through normalization

An integral birational morphism of decent algebraic spaces with finitely many
irreducible components receives the absolute normalization of its target, and
the resulting factor is identified with the absolute normalization of its
source.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Normalization

/-- Lemma 68.22.9: Let `S` be a scheme. Let `f : X ⟶ Y` be an integral
birational morphism of decent algebraic spaces over `S` which have finitely
many irreducible components. Then there is a factorization
`β : Y.normalization ⟶ X` of `Y.normalizationTo` through `f`, and an
isomorphism `e : Y.normalization ≅ X.normalization` identifying `β` with
`X.normalizationTo`. -/
@[stacks 0BBH]
theorem exists_factorization {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] [IsIntegralHom f] :
    ∃ (β : Y.normalization ⟶ X) (e : Y.normalization ≅ X.normalization),
      β ≫ f = Y.normalizationTo ∧ β = e.hom ≫ X.normalizationTo :=
  sorry

/-- A morphism `β : Y.normalization ⟶ X` factoring `Y.normalizationTo` through
an integral birational morphism `f : X ⟶ Y` of decent algebraic spaces with
finitely many irreducible components is identified with `X.normalizationTo` by
an isomorphism `Y.normalization ≅ X.normalization`. -/
theorem iso_of_factor {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] [IsIntegralHom f]
    {β : Y.normalization ⟶ X} (hβ : β ≫ f = Y.normalizationTo) :
    ∃ e : Y.normalization ≅ X.normalization, β = e.hom ≫ X.normalizationTo :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Normalization
