module

public import stacks_project.Chap67.Lemma_67_23_2
public import stacks_project.Chap72.Definition_72_5_2

/-!
# Composition of degrees of morphisms of integral algebraic spaces

The degree of a composite dominant locally finite type morphism of integral
algebraic spaces is the product of the degrees, matching the tower law for
finite residue-field extensions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

namespace Dominant

/-- The composition of dominant morphisms of algebraic spaces is dominant. -/
instance comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y)
    (g : Y ⟶ Z) [Dominant f] [Dominant g] : Dominant (f ≫ g) :=
  sorry

end Dominant

namespace Hom

/-- Residue degrees multiply along a tower of residue-field extensions of
decent algebraic spaces. -/
theorem residueDegree_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] [IsDecent Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Points X) :
    residueDegree (f ≫ g) x =
      residueDegree f x * residueDegree g (Points.map f x) :=
  sorry

/-- Finite residue-field extensions of integral algebraic spaces are closed
under composition of dominant morphisms. -/
theorem finiteResidueFieldExtension_comp {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Dominant f] [Dominant g]
    (hf : FiniteResidueFieldExtension f) (hg : FiniteResidueFieldExtension g) :
    FiniteResidueFieldExtension (f ≫ g) :=
  sorry

/-- Lemma 72.5.3: Let `S` be a scheme. Let `X`, `Y`, `Z` be integral algebraic
spaces over `S`. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be dominant morphisms
locally of finite type. Assume any of the equivalent conditions (1)–(5) of
Lemma 72.5.1, equivalently `FiniteResidueFieldExtension`, hold for `f` and
`g`. Then `degree (f ≫ g) = degree f * degree g`. In source notation this is
`deg(X/Z) = deg(X/Y) * deg(Y/Z)`. -/
@[stacks 0ENH]
theorem degree_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [Dominant f] [Dominant g]
    (hf : FiniteResidueFieldExtension f) (hg : FiniteResidueFieldExtension g) :
    degree (f ≫ g) = degree f * degree g :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
