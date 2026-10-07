module

public import stacks_project.Chap100.Lemma_100_3_5_LocalAtSource
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

/- Lemma 100.3.5 (1): if `P` is étale-local on the source and `f` is a
surjective étale 1-morphism of algebraic stacks representable by algebraic
spaces, then `has P (f ≫ g)` implies `has P g`. -/
@[stacks 06M2] #check
  (has.of_comp_etale :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (P : MorphismProperty (AlgebraicSpace S))
      [P.IsStableUnderBaseChange]
      [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
      [P.IsLocalAtSource AlgebraicSpace.etalePrecoverage]
      {f : X ⟶ Y} {g : Y ⟶ Z} [Etale f] [Surjective f],
      relativelyRepresentableByAlgebraicSpaces g → has P (f ≫ g) → has P g)

/- Lemma 100.3.5 (2): if `P` is smooth-local on the source and `f` is a
surjective smooth 1-morphism of algebraic stacks representable by algebraic
spaces, then `has P (f ≫ g)` implies `has P g`. -/
@[stacks 06M2] #check
  (has.of_comp_smooth :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (P : MorphismProperty (AlgebraicSpace S))
      [P.IsStableUnderBaseChange]
      [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
      [P.IsLocalAtSource (AlgebraicSpace.precoverage (@AlgebraicSpace.Smooth S))]
      {f : X ⟶ Y} {g : Y ⟶ Z} [Smooth f] [Surjective f],
      relativelyRepresentableByAlgebraicSpaces g → has P (f ≫ g) → has P g)

/- Lemma 100.3.5 (3): if `P` is syntomic-local on the source and `f` is a
surjective syntomic 1-morphism of algebraic stacks representable by algebraic
spaces, then `has P (f ≫ g)` implies `has P g`. -/
@[stacks 06M2] #check
  (has.of_comp_syntomic :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (P : MorphismProperty (AlgebraicSpace S))
      [P.IsStableUnderBaseChange]
      [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
      [P.IsLocalAtSource (AlgebraicSpace.precoverage (@AlgebraicSpace.Syntomic S))]
      {f : X ⟶ Y} {g : Y ⟶ Z},
      relativelyRepresentableByAlgebraicSpaces f →
        ∀ [Surjective f], has (@AlgebraicSpace.Syntomic S) f →
          relativelyRepresentableByAlgebraicSpaces g → has P (f ≫ g) → has P g)

/- Lemma 100.3.5 (4): if `P` is fppf-local on the source and `f` is a
surjective flat locally of finite presentation 1-morphism of algebraic stacks
representable by algebraic spaces, then `has P (f ≫ g)` implies `has P g`. -/
@[stacks 06M2] #check
  (has.of_comp_fppf :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (P : MorphismProperty (AlgebraicSpace S))
      [P.IsStableUnderBaseChange]
      [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
      [P.IsLocalAtSource (AlgebraicSpace.fppfPrecoverage S)]
      {f : X ⟶ Y} {g : Y ⟶ Z} [Flat f] [Surjective f],
      has (@AlgebraicSpace.LocallyOfFinitePresentation S) f →
        relativelyRepresentableByAlgebraicSpaces g → has P (f ≫ g) → has P g)
