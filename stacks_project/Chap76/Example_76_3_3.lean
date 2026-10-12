/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import stacks_project.Chap76.Example_76_3_3_Space

/-!
# Universally injective but not radicial

The structure morphism of `[Spec algebraicQ / Gal(algebraicQ / ℚ)]` over
`Spec ℚ` is universally injective, but not radicial.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient

/-- Example 76.3.3 (1): the structure morphism
`X = [Spec algebraicQ / Gal(algebraicQ / ℚ)] ⟶ S = Spec ℚ` of Spaces is
universally injective, in the sense that the relative diagonal is a
representable surjection. -/
@[stacks 0483]
theorem universallyInjective_toSpec :
    (MorphismProperty.over (@Surjective)).relative uliftYoneda.{1}
      (pullback.diagonal toSpec).hom := sorry

/-- Example 76.3.3 (2): the identity fibre of `toSpec` is the sheaf
`sheafOfPoints`, which is nonempty because the atlas `Spec algebraicQ ⟶ X`
supplies a section, and is not isomorphic over `Spec ℚ` to the `uliftYoneda`
sheaf of `Spec L` for any purely inseparable extension `L / ℚ`. -/
@[stacks 0483]
theorem not_radicial_toSpec :
    Nonempty (sheafOfPoints.obj.obj (op cover)) ∧
      ∀ (L : Type) [Field L] [Algebra ℚ L] [IsPurelyInseparable ℚ L]
        (e : sheafOfPoints ≅
          (Scheme.fppfTopology.over base).uliftYoneda.{1}.obj
            (Over.mk (FieldExtension.specMap ℚ L))),
        e.hom ≫ (Scheme.fppfTopology.over base).uliftYoneda.{1}.map (specToBase L) ≠
          toSpec := sorry

end AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient
