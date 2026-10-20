module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiAffine
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property
public import ReasLib.CategoryTheory.Fibered.Stack.Coverwise

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

/-- An algebraic stack `X` over a scheme `S` whose
1-morphism diagonal `Δ : X ⟶ X ×_S X` is quasi-affine is a stack in groupoids
on the big fpqc site of schemes over `S`. -/
@[stacks 0GRH]
theorem isStack_fpqc {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    (h_quasiAffineDiagonal : Groupoids.Hom.has (@AlgebraicSpace.QuasiAffine S)
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X)) :
    IsStack.InGroupoids (Scheme.fpqcTopology.over S) X.p := sorry

/-- For an algebraic stack with quasi-affine diagonal, the fiber functor
`X.p.Fiber U ⟶ DD(𝒰)` is an equivalence for every fpqc covering of schemes
over `S`. -/
theorem isStack_fpqc_coverwise {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X]
    (h_quasiAffineDiagonal : Groupoids.Hom.has (@AlgebraicSpace.QuasiAffine S)
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    (U : Over S) (T : (Scheme.fpqcTopology.over S).Cover U) :
    (Descent.functor T X.p).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicStack
