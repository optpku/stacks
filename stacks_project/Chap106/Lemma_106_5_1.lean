module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Thickening.Flat
import StacksCheckRecall

/-!
# Flatness of morphisms of thickenings of algebraic stacks
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory
open AlgebraicGeometry.AlgebraicStack

universe u

/- Lemma 106.5.1: in a 2-commutative triangle of thickenings of algebraic
stacks, with Y' ⟶ B' locally of finite type, X' ⟶ B' flat and locally of finite
presentation, f flat, and both vertical squares 2-fibre products, f' is flat
and Y' ⟶ B' is flat at every point of |Y'| in the image of |f'|. -/
@[stacks 0CJB] #check
  (AlgebraicGeometry.AlgebraicStack.IsThickening.flatAmbient_and_flatAtTarget :
    ∀ {S : Scheme.{u}} {X X' Y Y' B B' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      [AlgebraicStack B] [AlgebraicStack B']
      {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'}
      {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
      [IsThickening iX] [IsThickening iY] [IsThickening iB]
      [LocallyOfFiniteType pY'] [Flat pX'] [LocallyOfFinitePresentation pX'] [Flat f]
      (sq : IsThickening.Hom iX iY f f')
      (hX : IsThickening.Hom iX iB pX pX') (hY : IsThickening.Hom iY iB pY pY')
      (triangle : f ≫ pY ≅ pX) (triangle' : f' ≫ pY' ≅ pX')
      (pullbackX : PseudoPullbackCone.IsBilimit
        (⟨X, pX, iX, hX.w⟩ : PseudoPullbackCone iB pX'))
      (pullbackY : PseudoPullbackCone.IsBilimit
        (⟨Y, pY, iY, hY.w⟩ : PseudoPullbackCone iB pY')),
      Flat f' ∧
        (∀ y' : Points Y', y' ∈ Set.range (Points.map f') →
          existsFlatAtPointSquare pY' y'))
