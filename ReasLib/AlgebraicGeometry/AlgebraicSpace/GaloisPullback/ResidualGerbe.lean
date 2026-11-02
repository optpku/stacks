/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GaloisPullback.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteTypePoints
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Noetherian
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Monomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Monomorphism

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
theorem isFiniteTypePoint_xPoint : AlgebraicStack.IsFiniteTypePoint xPoint := by
  let p : AlgebraicStack.FieldValuedPoint toStack :=
    AlgebraicStack.FieldValuedPoint.of AlgebraicNumbers.algebraicQ (𝟙 base) pointHom
  letI : Groupoids.Hom.LocallyOfFiniteType p.hom := instLocallyOfFiniteType_pointHom
  exact ⟨p, inferInstance, rfl⟩

private theorem pointHom_full_faithful :
    (toFunctor pointHom).Full ∧ (toFunctor pointHom).Faithful := by
  letI : (GroupoidsOver.slice (Over.mk (𝟙 base))).p.Full := by
    change (Over.forget (Over.mk (𝟙 base))).Full
    exact ⟨fun f => ⟨Over.homMk f (Over.mkIdTerminal.hom_ext _ _), rfl⟩⟩
  letI : (GroupoidsOver.slice (Over.mk (𝟙 base))).p.Faithful := by
    change (Over.forget (Over.mk (𝟙 base))).Faithful
    infer_instance
  letI : toStack.p.Faithful := by
    change (CategoryOfElements.π sheafOfPoints.obj).leftOp.Faithful
    infer_instance
  exact ⟨Functor.Full.of_comp_faithful_iso
    (eqToIso (FiberedCategoryOver.Groupoids.comm pointHom)),
    Functor.Faithful.of_comp_eq (FiberedCategoryOver.Groupoids.comm pointHom)⟩

/-- As an algebraic space over `AlgebraicNumbers.algebraicQ`, the morphism
`x` is a monomorphism. -/
instance instMono_pointHom : Groupoids.Hom.Mono pointHom := by
  apply Groupoids.Hom.Mono.of_fullyFaithful
  letI := pointHom_full_faithful.1
  letI := pointHom_full_faithful.2
  exact ⟨Functor.FullyFaithful.ofFullyFaithful _⟩

/-- `x` is not an isomorphism of algebraic stacks. -/
theorem not_isEquivalence_pointHom :
    ¬ (toBasedFunctor pointHom).IsEquivalence := sorry

/-- The source `Spec AlgebraicNumbers.algebraicQ` is a singleton on points. -/
instance instSubsingleton_points_slice_base :
    Subsingleton (AlgebraicStack.Points (GroupoidsOver.slice (Over.mk (𝟙 base)))) := by
  refine ⟨fun x y => ?_⟩
  apply AlgebraicStack.Points.map_injective_of_mono pointHom
  exact Subsingleton.elim _ _

private theorem pointHom_image_eq_singleton :
    Set.range (AlgebraicStack.Points.map pointHom) = {xPoint} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact Set.mem_singleton_iff.mpr (Subsingleton.elim _ _)
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    let p : AlgebraicStack.FieldValuedPoint
        (GroupoidsOver.slice (Over.mk (𝟙 base))) :=
      AlgebraicStack.FieldValuedPoint.of AlgebraicNumbers.algebraicQ (𝟙 base) (𝟙 _)
    exact ⟨AlgebraicStack.Points.mk p, rfl⟩

/-- `Spec AlgebraicNumbers.algebraicQ ⟶ X` is the residual gerbe of `X` at
`x`. -/
instance instIsResidualGerbe_pointHom : AlgebraicStack.IsResidualGerbe pointHom xPoint := by
  letI : AlgebraicGeometry.IsReduced (Over.mk (𝟙 base)).left := by
    change AlgebraicGeometry.IsReduced base
    letI : _root_.IsReduced (CommRingCat.of AlgebraicNumbers.algebraicQ) := by
      change _root_.IsReduced AlgebraicNumbers.algebraicQ
      infer_instance
    exact inferInstance
  apply (AlgebraicStack.IsResidualGerbe.iff pointHom xPoint).mpr
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    pointHom_image_eq_singleton⟩

/-- The essential image of the canonical point morphism agrees with that of the
residual-gerbe inclusion. -/
theorem pointHom_essImage_eq_residualGerbeι :
    (toFunctor pointHom).essImage =
      (toFunctor (AlgebraicStack.residualGerbeι toStack xPoint)).essImage := by
  let p : AlgebraicStack.FieldValuedPoint
      (GroupoidsOver.slice (Over.mk (𝟙 base))) :=
    AlgebraicStack.FieldValuedPoint.of AlgebraicNumbers.algebraicQ (𝟙 base) (𝟙 _)
  letI : Nonempty (AlgebraicStack.Points
      (GroupoidsOver.slice (Over.mk (𝟙 base)))) := ⟨AlgebraicStack.Points.mk p⟩
  letI : AlgebraicGeometry.IsReduced (Over.mk (𝟙 base)).left := by
    change AlgebraicGeometry.IsReduced base
    letI : _root_.IsReduced (CommRingCat.of AlgebraicNumbers.algebraicQ) := by
      change _root_.IsReduced AlgebraicNumbers.algebraicQ
      infer_instance
    exact inferInstance
  apply AlgebraicStack.residualGerbe_essImage_unique pointHom pointHom_full_faithful
  exact pointHom_image_eq_singleton

end AlgebraicGeometry.AlgebraicSpace.GaloisPullback
