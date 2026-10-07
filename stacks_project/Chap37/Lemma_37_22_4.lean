module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Lemma 37.22.4 (1): Cohen--Macaulayness at compatible points is preserved
by composition when the fibres of both morphisms and their composite are
locally Noetherian. -/
@[stacks 0C0W] #check
  (AlgebraicGeometry.Scheme.Hom.CohenMacaulayAt.comp :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
        [∀ y : Y, IsLocallyNoetherian (f.fiber y)]
        [∀ z : Z, IsLocallyNoetherian (g.fiber z)]
        [∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z)],
      f.CohenMacaulayAt x → g.CohenMacaulayAt (f x) →
        (f ≫ g).CohenMacaulayAt x)

/- Lemma 37.22.4 (2): the composite of Cohen--Macaulay morphisms is
Cohen--Macaulay when all three fibre families are locally Noetherian. -/
@[stacks 0C0W] #check
  (AlgebraicGeometry.CohenMacaulay.comp :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
        [∀ y : Y, IsLocallyNoetherian (f.fiber y)]
        [∀ z : Z, IsLocallyNoetherian (g.fiber z)]
        [∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z)]
        [CohenMacaulay f] [CohenMacaulay g],
      CohenMacaulay (f ≫ g))

/- Lemma 37.22.4 (3): if a composite is Cohen--Macaulay at `x` and its first
factor is flat there, then both factors are Cohen--Macaulay at the corresponding
points. -/
@[stacks 0C0W] #check
  (AlgebraicGeometry.Scheme.Hom.CohenMacaulayAt.of_comp_of_flatAt :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
        [∀ y : Y, IsLocallyNoetherian (f.fiber y)]
        [∀ z : Z, IsLocallyNoetherian (g.fiber z)]
        [∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z)],
      (f ≫ g).CohenMacaulayAt x → f.flatAt x →
        f.CohenMacaulayAt x ∧ g.CohenMacaulayAt (f x))

/- Lemma 37.22.4 (4): if a composite is Cohen--Macaulay and its first factor
is flat, then the first factor is Cohen--Macaulay and the second is
Cohen--Macaulay at every point in the image of the first. -/
@[stacks 0C0W] #check
  (AlgebraicGeometry.CohenMacaulay.of_comp_of_flat :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
        [∀ y : Y, IsLocallyNoetherian (f.fiber y)]
        [∀ z : Z, IsLocallyNoetherian (g.fiber z)]
        [∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z)]
        [CohenMacaulay (f ≫ g)] [Flat f],
      CohenMacaulay f ∧
        ∀ y : Y, y ∈ Set.range f → g.CohenMacaulayAt y)

end AlgebraicGeometry
