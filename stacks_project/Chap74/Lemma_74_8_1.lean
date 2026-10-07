module

public import stacks_project.Chap74.Lemma_74_8_1_Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 74.8.1 (1): if `f ≫ g` is a flat morphism of algebraic spaces over `S`
and `f` is a surjection of sheaves on `(Sch/S)_fppf`, then `g` is flat. -/
@[stacks 06NR] #check
  (AlgebraicGeometry.AlgebraicSpace.Flat.of_comp_of_isLocallySurjective :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [AlgebraicGeometry.AlgebraicSpace.Flat (f ≫ g)]
      [Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) f],
      AlgebraicGeometry.AlgebraicSpace.Flat g)

/- Lemma 74.8.1 (2): if `f ≫ g` is locally of finite type as a morphism of
algebraic spaces over `S` and `f` is a surjection of sheaves on `(Sch/S)_fppf`,
then `g` is locally of finite type. -/
@[stacks 06NR] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.of_comp_of_isLocallySurjective :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType (f ≫ g)]
      [Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) f],
      AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType g)

/- Lemma 74.8.1 (3): if `f ≫ g` is locally of finite presentation as a morphism
of algebraic spaces over `S` and `f` is a surjection of sheaves on
`(Sch/S)_fppf`, then `g` is locally of finite presentation. -/
@[stacks 06NR] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation.of_comp_of_isLocallySurjective :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation (f ≫ g)]
      [Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) f],
      AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation g)
