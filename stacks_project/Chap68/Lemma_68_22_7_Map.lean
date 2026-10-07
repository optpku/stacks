module

public import stacks_project.Chap68.Definition_68_22_1_Birational
public import stacks_project.Chap68.Lemma_68_22_7_Normalization

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
theorem exists_normalizationMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] :
    ∃ g : X.normalization ⟶ Y.normalization,
      g ≫ Y.normalizationTo = X.normalizationTo ≫ f ∧ IsBirational g :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsBirational
