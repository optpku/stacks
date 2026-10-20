module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Birational

/-!
# Induced birational maps of absolute normalizations

A birational morphism of decent algebraic spaces with finitely many irreducible
components sends codimension-`0` points to codimension-`0` points, and therefore
lifts through absolute normalizations to a birational morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsBirational

/-- A birational morphism of decent algebraic spaces with finitely many
irreducible components sends codimension-`0` points to codimension-`0` points. -/
theorem mapsCodimZero {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    {f : X ⟶ Y} [IsBirational f] :
    AlgebraicGeometry.AlgebraicSpace.mapsCodimZero f :=
  sorry

/-- A morphism of absolute normalizations commuting with a birational morphism
of decent algebraic spaces with finitely many irreducible components is
birational. -/
theorem of_comp_normalizationTo {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] {g : X.normalization ⟶ Y.normalization}
    (h : g ≫ Y.normalizationTo = X.normalizationTo ≫ f) :
    IsBirational g :=
  sorry

/-- A birational morphism of decent algebraic spaces with finitely many
irreducible components lifts through absolute normalizations to a birational
morphism making the square with `normalizationTo` commute. -/
@[stacks 0BBG]
theorem exists_normalizationMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] :
    ∃ g : X.normalization ⟶ Y.normalization,
      g ≫ Y.normalizationTo = X.normalizationTo ≫ f ∧ IsBirational g :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsBirational

namespace AlgebraicGeometry.AlgebraicSpace.Normalization

/-- An integral birational morphism of decent algebraic spaces with finitely
many irreducible components receives the absolute normalization of its target,
and this factor is identified with the absolute normalization of its source
by an isomorphism compatible with the normalization morphisms. -/
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
