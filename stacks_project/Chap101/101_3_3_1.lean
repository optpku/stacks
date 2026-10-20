module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Diagonal
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry Opposite
open FiberedCategoryOver.Groupoids
open CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal
open CategoryTheory.Limits
open scoped Bicategory

noncomputable section

universe u

/- 101.3.3.1: The diagonal base change along a Yoneda triple is the fibre square
of Isom sheaves over the test scheme. -/
@[stacks 04XT] #check (AlgebraicGeometry.AlgebraicStack.isomSquare_isPullback : ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {T : Over S}
    (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x'),
    IsPullback (toIsom f x x' α) (toBase f x x' α)
      (isomMap f x x') (alphaSection f x x' α))

#check (AlgebraicGeometry.AlgebraicStack.diagonal_isom_isSheaf : ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {T : Over S} (x x' : X.p.Fiber T),
    Presheaf.IsSheaf ((Scheme.fppfTopology.over S).over T) (isom x x'))

#check (AlgebraicGeometry.AlgebraicStack.diagonal_base_isSheaf : ∀ {S : Scheme.{u}} (T : Over S),
    Presheaf.IsSheaf ((Scheme.fppfTopology.over S).over T)
      (yoneda.obj (Over.mk (𝟙 T)) ⋙ uliftFunctor.{u + 1, u}))

#check (AlgebraicGeometry.AlgebraicStack.diagonal_apexSheaf_isSheaf : ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {T : Over S}
    (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x'),
    Presheaf.IsSheaf ((Scheme.fppfTopology.over S).over T) (apexSheaf f x x' α))

