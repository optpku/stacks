module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.SmallEtaleComparison

/-!
# Small étale comparison of a representing algebraic space

The comparison functor sends an étale chart to its image under a chosen
representing equivalence.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Bicategory

universe u

variable {S : Scheme.{u}}
variable (F : AlgebraicSpace S) (X : GroupoidsOver S) (e : F.toGroupoids ≌ X)

#check (AlgebraicGeometry.GroupoidsOver.smallEtaleFunctor F X e :
  AlgebraicSpace.smallEtaleSite F ⥤ X.total)
