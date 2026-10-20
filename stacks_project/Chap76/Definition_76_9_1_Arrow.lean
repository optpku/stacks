module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.Arrow
import StacksCheckRecall

open CategoryTheory

universe u

/- Definition 76.9.1: thickenings of algebraic spaces form the category of
arrows whose defining morphism is a thickening. -/
@[stacks 05ZK] #check (AlgebraicGeometry.AlgebraicSpace.Thickening :
  AlgebraicGeometry.Scheme.{u} → Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.homMk :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S} →
      (f : T.left ⟶ U.left) → (f' : T.right ⟶ U.right) →
        f ≫ U.hom = T.hom ≫ f' → (T ⟶ U))

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.Over :
  {S : AlgebraicGeometry.Scheme.{u}} →
    AlgebraicGeometry.AlgebraicSpace S → Type (u + 1))
