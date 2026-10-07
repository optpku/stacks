module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Descent of stacks in setoids along an fppf algebraic-space cover

If a stack in groupoids over `(Sch/S)_fppf` is covered by an fppf morphism of
algebraic spaces and the 2-fibre product is a stack in setoids, then the original
stack is a stack in setoids.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace CategoryTheory.IsStack.InSetoids

/-- Lemma 97.4.2: Let `X`, `Y`, `Z` be stacks in groupoids over `(Sch/S)_fppf`,
and let `f : X ⟶ Z.toGroupoids` be an arbitrary 1-morphism. If `Y`, `Z` are represented by
algebraic spaces over `S`, the associated morphism of algebraic spaces
`φ : Y ⟶ Z` is surjective, flat, and locally of finite presentation, and the
2-fibre product `Y ×_Z X` is a stack in setoids, then `X` is a stack in setoids. -/
@[stacks 05XL]
theorem of_fppfAlgebraicSpacePullback
    {S : Scheme.{u}} {X : GroupoidsOver S} {Y Z : AlgebraicSpace S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    (f : X ⟶ Z.toGroupoids) (φ : Y ⟶ Z)
    [AlgebraicSpace.Surjective φ] [AlgebraicSpace.Flat φ]
    [AlgebraicSpace.LocallyOfFinitePresentation φ]
    [IsStack.InSetoids (Scheme.fppfTopology.over S)
      (FiberedCategoryOver.Groupoids.p
        (TwoFibreProduct.apex.{u + 1, u, u + 1, u}
          (AlgebraicSpace.toGroupoids.map φ)
          f))] :
    IsStack.InSetoids (Scheme.fppfTopology.over S) X.p :=
  sorry

end CategoryTheory.IsStack.InSetoids
