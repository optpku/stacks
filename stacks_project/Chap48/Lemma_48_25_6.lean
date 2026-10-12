/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Lemma 48.25.6 (1): Gorensteinness at compatible points is preserved by
composition when the fibres of both morphisms and their composite are locally
Noetherian. -/
@[stacks 0C11] #check
  (AlgebraicGeometry.Scheme.Hom.gorensteinAt.comp :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
        [∀ y : Y, IsLocallyNoetherian (f.fiber y)]
        [∀ z : Z, IsLocallyNoetherian (g.fiber z)]
        [∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z)],
      f.gorensteinAt x → g.gorensteinAt (f x) →
        (f ≫ g).gorensteinAt x)

/- Lemma 48.25.6 (2): the composite of Gorenstein morphisms is Gorenstein when
all three fibre families are locally Noetherian. -/
@[stacks 0C11] #check
  (AlgebraicGeometry.Gorenstein.comp :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
        [∀ y : Y, IsLocallyNoetherian (f.fiber y)]
        [∀ z : Z, IsLocallyNoetherian (g.fiber z)]
        [∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z)]
        [Gorenstein f] [Gorenstein g],
      Gorenstein (f ≫ g))

/- Lemma 48.25.6 (3): if a composite is Gorenstein at `x` and its first factor
is flat there, then both factors are Gorenstein at the corresponding points. -/
@[stacks 0C11] #check
  (AlgebraicGeometry.Scheme.Hom.gorensteinAt.of_comp_of_flatAt :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
        [∀ y : Y, IsLocallyNoetherian (f.fiber y)]
        [∀ z : Z, IsLocallyNoetherian (g.fiber z)]
        [∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z)],
      (f ≫ g).gorensteinAt x → f.flatAt x →
        f.gorensteinAt x ∧ g.gorensteinAt (f x))

/- Lemma 48.25.6 (4): if a composite is Gorenstein and its first factor is
flat, then the first factor is Gorenstein and the second is Gorenstein at every
point in the image of the first. -/
@[stacks 0C11] #check
  (AlgebraicGeometry.Gorenstein.of_comp_of_flat :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
        [∀ y : Y, IsLocallyNoetherian (f.fiber y)]
        [∀ z : Z, IsLocallyNoetherian (g.fiber z)]
        [∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z)]
        [Gorenstein (f ≫ g)] [Flat f],
      Gorenstein f ∧
        ∀ y : Y, y ∈ Set.range f → g.gorensteinAt y)

end AlgebraicGeometry
