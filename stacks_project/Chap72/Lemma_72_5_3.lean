/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dominant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField.Degree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Degree
import StacksCheckRecall

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

#check (AlgebraicGeometry.AlgebraicSpace.Dominant.comp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Dominant f] [Dominant g], Dominant (f ≫ g))

namespace Hom

#check (AlgebraicGeometry.AlgebraicSpace.Hom.residueDegree_comp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] [IsDecent Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Points X),
    residueDegree (f ≫ g) x =
      residueDegree f x * residueDegree g (Points.map f x))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.finiteResidueFieldExtension_comp :
  ∀ {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Dominant f] [Dominant g]
    (hf : FiniteResidueFieldExtension f) (hg : FiniteResidueFieldExtension g),
    FiniteResidueFieldExtension (f ≫ g))

/- Lemma 72.5.3: Let `S` be a scheme. Let `X`, `Y`, `Z` be integral algebraic
spaces over `S`. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be dominant morphisms
locally of finite type. Assume any of the equivalent conditions (1)–(5) of
Lemma 72.5.1, equivalently `FiniteResidueFieldExtension`, hold for `f` and
`g`. Then `degree (f ≫ g) = degree f * degree g`. In source notation this is
`deg(X/Z) = deg(X/Y) * deg(Y/Z)`. -/
@[stacks 0ENH] #check (AlgebraicGeometry.AlgebraicSpace.Hom.degree_comp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [Dominant f] [Dominant g]
    (hf : FiniteResidueFieldExtension f) (hg : FiniteResidueFieldExtension g),
    degree (f ≫ g) = degree f * degree g)

end Hom

end AlgebraicGeometry.AlgebraicSpace
