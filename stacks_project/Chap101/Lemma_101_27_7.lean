module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FinitePresentation.Diagonal
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Lemma 101.27.7 (1): if `f : X ⟶ Y` is locally of finite type, then its
diagonal `Hom.diagonal f : X ⟶ X ×_Y X` is locally of finite presentation. -/
@[stacks 0CMG] #check
  (AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation.diagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
      [LocallyOfFiniteType f],
      LocallyOfFinitePresentation (Hom.diagonal.{u + 1, u, u + 1} f))

/- Lemma 101.27.7 (2): if `f : X ⟶ Y` is quasi-separated and locally of finite
type, then its diagonal `Hom.diagonal f : X ⟶ X ×_Y X` is of finite
presentation. -/
@[stacks 0CMG] #check
  (AlgebraicGeometry.AlgebraicStack.FinitePresentation.diagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
      [QuasiSeparated f] [LocallyOfFiniteType f],
      FinitePresentation (Hom.diagonal.{u + 1, u, u + 1} f))
