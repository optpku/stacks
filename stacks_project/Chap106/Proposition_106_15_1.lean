module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Fpqc
import StacksCheckRecall

/-!
# Algebraic stacks with quasi-affine diagonal and fpqc descent

An algebraic stack over a scheme `S` whose diagonal is quasi-affine satisfies
descent for fpqc coverings of schemes over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open GrothendieckTopology.Cover
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Proposition 106.15.1. An algebraic stack `X` over a scheme `S` whose
1-morphism diagonal `Δ : X ⟶ X ×_S X` is quasi-affine is a stack in groupoids
on the big fpqc site of schemes over `S`. -/
@[stacks 0GRH] #check (AlgebraicGeometry.AlgebraicStack.isStack_fpqc :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    (h_quasiAffineDiagonal : Groupoids.Hom.has (@AlgebraicSpace.QuasiAffine S)
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X)),
    IsStack.InGroupoids (Scheme.fpqcTopology.over S) X.p)

/- For an algebraic stack with quasi-affine diagonal, the fiber functor
`X.p.Fiber U ⟶ DD(𝒰)` is an equivalence for every fpqc covering of schemes
over `S`. -/
#check (AlgebraicGeometry.AlgebraicStack.isStack_fpqc_coverwise :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X]
    (h_quasiAffineDiagonal : Groupoids.Hom.has (@AlgebraicSpace.QuasiAffine S)
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    (U : Over S) (T : (Scheme.fpqcTopology.over S).Cover U),
    (Descent.functor T X.p).IsEquivalence)

end AlgebraicGeometry.AlgebraicStack
