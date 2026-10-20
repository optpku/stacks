module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GaloisPullback.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteTypePoints
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Noetherian
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Monomorphism

/-!
# A non-Noetherian one-point algebraic space and its residual gerbe

The fppf quotient `X = U / G` of the Galois pullback
`U = Spec AlgebraicNumbers.algebraicQ ×_{Spec ℚ} Spec AlgebraicNumbers.algebraicQ` is a reduced algebraic space
with a unique point, and is not locally Noetherian. The composite
`x : Spec AlgebraicNumbers.algebraicQ ⟶ U ⟶ X` is a locally finite type monomorphism which is
the residual gerbe at that unique point, but is not an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.GaloisPullback
open AlgebraicGeometry.AlgebraicStack
open FiberedCategoryOver.Groupoids (toFunctor toBasedFunctor)
open scoped Bicategory

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.GaloisPullback

/-- The quotient `X = U / G` is an algebraic space over
`Spec AlgebraicNumbers.algebraicQ`, hence an algebraic stack. -/
instance instAlgebraicStack_toStack : AlgebraicStack toStack := sorry

/-- The field-valued point `x : Spec AlgebraicNumbers.algebraicQ ⟶ X`. -/
def xPoint : AlgebraicStack.Points toStack :=
  AlgebraicStack.Points.mk (AlgebraicStack.FieldValuedPoint.of AlgebraicNumbers.algebraicQ (𝟙 base) pointHom)

/-- `xPoint` is the class of the field-valued point given by `pointHom`. -/
theorem xPoint_eq :
    xPoint = AlgebraicStack.Points.mk (AlgebraicStack.FieldValuedPoint.of AlgebraicNumbers.algebraicQ (𝟙 base) pointHom) :=
  rfl

/-- `X` is reduced. -/
instance instIsReduced_toStack : AlgebraicStack.IsReduced toStack := sorry

/-- `X` is nonempty on points. -/
instance instNonempty_points_toStack : Nonempty (AlgebraicStack.Points toStack) := ⟨xPoint⟩

/-- `X` has exactly one point. -/
instance instSubsingleton_points_toStack : Subsingleton (AlgebraicStack.Points toStack) := sorry

/-- `X` is not locally Noetherian. -/
theorem not_isLocallyNoetherian : ¬ AlgebraicStack.IsLocallyNoetherian toStack := sorry

/-- The morphism `x` is locally of finite type. -/
instance instLocallyOfFiniteType_pointHom :
    Groupoids.Hom.LocallyOfFiniteType pointHom := sorry

/-- `x` is a locally finite type point of `X`. -/
theorem isFiniteTypePoint_xPoint : AlgebraicStack.IsFiniteTypePoint xPoint := sorry

/-- As an algebraic space over `AlgebraicNumbers.algebraicQ`, the morphism
`x` is a monomorphism. -/
instance instMono_pointHom : Groupoids.Hom.Mono pointHom := sorry

/-- `x` is not an isomorphism of algebraic stacks. -/
theorem not_isEquivalence_pointHom :
    ¬ (toBasedFunctor pointHom).IsEquivalence := sorry

/-- The source `Spec AlgebraicNumbers.algebraicQ` is a singleton on points. -/
instance instSubsingleton_points_slice_base :
    Subsingleton (AlgebraicStack.Points (GroupoidsOver.slice (Over.mk (𝟙 base)))) := sorry

/-- `Spec AlgebraicNumbers.algebraicQ ⟶ X` is the residual gerbe of `X` at
`x`. -/
instance instIsResidualGerbe_pointHom : AlgebraicStack.IsResidualGerbe pointHom xPoint := sorry

/-- The essential image of the canonical point morphism agrees with that of the
residual-gerbe inclusion. -/
theorem pointHom_essImage_eq_residualGerbeι :
    (toFunctor pointHom).essImage =
      (toFunctor (AlgebraicStack.residualGerbeι toStack xPoint)).essImage := sorry

end AlgebraicGeometry.AlgebraicSpace.GaloisPullback
