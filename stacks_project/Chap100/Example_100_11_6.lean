module

public import stacks_project.Chap100.Definition_100_8_1_Mono
public import stacks_project.Chap100.Definition_100_11_8_ResidualGerbe
public import stacks_project.Chap100.Example_100_11_6_Cover
public import stacks_project.Chap100.Example_100_11_6_Quotient
public import stacks_project.Chap100.Example_100_11_9_ResidualGerbe
public import stacks_project.Chap100.Lemma_100_11_2_LocallyOfFiniteType
public import stacks_project.Chap100.Lemma_100_11_2_Reduced
public import stacks_project.Chap100.Lemma_100_11_3_LocallyNoetherian
public import stacks_project.Chap101.Lemma_101_18_4_FiniteTypePoint

/-!
# A non-Noetherian residual gerbe that is an algebraic space

The fppf quotient `X = U / G` of the Galois pullback
`U = Spec algebraicQ ×_{Spec ℚ} Spec algebraicQ` is a reduced algebraic space
with a unique point, and is not locally Noetherian. The composite
`x : Spec algebraicQ ⟶ U ⟶ X` is a locally finite type monomorphism which is
the residual gerbe at that unique point, but is not an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient
open AlgebraicGeometry.AlgebraicSpace.GaloisPullback
open AlgebraicGeometry.AlgebraicStack
open FiberedCategoryOver.Groupoids (toFunctor toBasedFunctor)
open scoped Bicategory

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.GaloisPullback

/-- Example 100.11.6 (1): the quotient `X = U / G` is an algebraic space over
`Spec algebraicQ`, hence an algebraic stack. -/
@[stacks 06MS, instance]
instance instAlgebraicStack_toStack : AlgebraicStack toStack := sorry

/-- The field-valued point `x : Spec algebraicQ ⟶ X`. -/
def xPoint : AlgebraicStack.Points toStack :=
  AlgebraicStack.Points.mk (AlgebraicStack.FieldValuedPoint.of algebraicQ (𝟙 base) pointHom)

/-- `xPoint` is the class of the field-valued point given by `pointHom`. -/
theorem xPoint_eq :
    xPoint = AlgebraicStack.Points.mk (AlgebraicStack.FieldValuedPoint.of algebraicQ (𝟙 base) pointHom) :=
  sorry

/-- Example 100.11.6 (1): `X` is reduced. -/
@[stacks 06MS, instance]
instance instIsReduced_toStack : AlgebraicStack.IsReduced toStack := sorry

/-- Example 100.11.6 (1): `X` is nonempty on points. -/
@[stacks 06MS, instance]
instance instNonempty_points_toStack : Nonempty (AlgebraicStack.Points toStack) := sorry

/-- Example 100.11.6 (1): `X` has exactly one point. -/
@[stacks 06MS, instance]
instance instSubsingleton_points_toStack : Subsingleton (AlgebraicStack.Points toStack) := sorry

/-- Example 100.11.6 (2): `X` is not locally Noetherian. -/
@[stacks 06MS]
theorem not_isLocallyNoetherian : ¬ AlgebraicStack.IsLocallyNoetherian toStack := sorry

/-- Example 100.11.6 (3): every point of `U` is closed. -/
@[stacks 06MS]
theorem mem_closedPoints_cover_left (u : cover.left) :
    u ∈ closedPoints cover.left := sorry

/-- Example 100.11.6 (3): the morphism `x` is locally of finite type. -/
@[stacks 06MS, instance]
instance instLocallyOfFiniteType_pointHom :
    Groupoids.Hom.LocallyOfFiniteType pointHom := sorry

/-- Example 100.11.6 (3): `x` is a locally finite type point of `X`. -/
@[stacks 06MS]
theorem isFiniteTypePoint_xPoint : AlgebraicStack.IsFiniteTypePoint xPoint := sorry

/-- Example 100.11.6 (4): as an algebraic space over `algebraicQ`, the morphism
`x` is a monomorphism. -/
@[stacks 06MS, instance]
instance instMono_pointHom : Groupoids.Hom.Mono pointHom := sorry

/-- Example 100.11.6 (4): `x` is not an isomorphism of algebraic stacks. -/
@[stacks 06MS]
theorem not_isEquivalence_pointHom :
    ¬ (toBasedFunctor pointHom).IsEquivalence := sorry

/-- The source `Spec algebraicQ` is a singleton on points. -/
instance instSubsingleton_points_slice_base :
    Subsingleton (AlgebraicStack.Points (GroupoidsOver.slice (Over.mk (𝟙 base)))) := sorry

/-- The residual gerbe of `X` at `x` exists. -/
instance instHasResidualGerbe_xPoint : AlgebraicStack.HasResidualGerbe toStack xPoint := sorry

/-- Example 100.11.6 (5): `Spec algebraicQ ⟶ X` is the residual gerbe of `X` at
`x`. -/
@[stacks 06MS, instance]
instance instIsResidualGerbe_pointHom : AlgebraicStack.IsResidualGerbe pointHom xPoint := sorry

/-- Example 100.11.6 (4): `x` is the morphism constructed in Lemma 100.11.5:
the essential image of `pointHom` agrees with that of the residual-gerbe
inclusion. -/
@[stacks 06MS]
theorem pointHom_essImage_eq_residualGerbeι :
    (toFunctor pointHom).essImage =
      (toFunctor (AlgebraicStack.residualGerbeι toStack xPoint)).essImage := sorry

end AlgebraicGeometry.AlgebraicSpace.GaloisPullback
