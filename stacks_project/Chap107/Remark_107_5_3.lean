module

public import stacks_project.Chap67.Lemma_67_34_3_FiberDimension
public import stacks_project.Chap107.Remark_107_5_3_RelativeDimension

/-!
# Well-definedness of relative dimension for space-to-stack morphisms

The quantity `dim_t(T_x)` of a locally of finite type morphism from an algebraic
space to an algebraic stack is independent of the representing fibre, and agrees
with Morphisms of Spaces Definition 67.33.1 when the target is an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Remark 107.5.3 (1): for a locally of finite type morphism `f : T ⟶ X` from
an algebraic space to an algebraic stack, the relative dimension `dim_t(T_x)` is
independent of the representing field-valued point of `x` and of the lift `t'`
to `T ×_X Spec k`, by invariance of relative dimension of locally of finite type
morphisms of schemes under base change (Morphisms Lemma 29.28.3). -/
@[stacks 0DRH]
theorem fiberDimensionAt_independent {S : Scheme.{u}} {T : AlgebraicSpace S}
    {X : GroupoidsOver S} [AlgebraicStack X] (f : T.toGroupoids ⟶ X)
    [LocallyOfFiniteType f] (t : AlgebraicSpace.Points T)
    (w w' : RelativeDimensionChoice f t) : w.dimension = w'.dimension :=
  sorry

/-- Remark 107.5.3 (2): if `X` is itself an algebraic space, then `dim_t(T_x)`
agrees with the relative dimension of Morphisms of Spaces Definition 67.33.1. -/
@[stacks 0DRH]
theorem fiberDimensionAt_eq_of_algebraicSpace {S : Scheme.{u}}
    {T Y : AlgebraicSpace S} (φ : T ⟶ Y) [AlgebraicSpace.LocallyOfFiniteType φ]
    (t : AlgebraicSpace.Points T)
    (w : RelativeDimensionChoice (AlgebraicSpace.toGroupoids.map φ) t) :
    w.dimension = AlgebraicSpace.fiberDimensionAt φ t :=
  sorry

end AlgebraicGeometry.AlgebraicStack
