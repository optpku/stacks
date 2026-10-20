module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.CategoryTheory.Adjunction.RelativeCupProduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor/naive-cup comparison

The comparison square is a categorical bridge between a tensorator on a right adjoint and a
concrete tensor construction on representatives.  It is independent of derived-category models;
those models enter only through the four maps supplied by an application.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uSource uTarget vSource vTarget wSource wTarget

namespace CategoryTheory

variable {SourceDerived : Type uSource} [Category.{vSource} SourceDerived]
variable {TargetDerived : Type uTarget} [Category.{vTarget} TargetDerived]

variable {leftDerivedPullback : TargetDerived ⥤ SourceDerived}
  {rightDerivedPushforward : SourceDerived ⥤ TargetDerived}
  (pullPushAdj : leftDerivedPullback ⊣ rightDerivedPushforward)
  (tensorSource : SourceDerived ⥤ SourceDerived ⥤ SourceDerived)
  (tensorTarget : TargetDerived ⥤ TargetDerived ⥤ TargetDerived)
  (pullbackTensorIso :
    ∀ (K L : TargetDerived),
      leftDerivedPullback.obj ((tensorTarget.obj L).obj K) ≅
        ((tensorSource.obj (leftDerivedPullback.obj L)).obj
          (leftDerivedPullback.obj K)))

variable {SourceComplex : Type wSource} {TargetComplex : Type wTarget}

variable
  (sourceComplexToDerived : SourceComplex → SourceDerived)
  (targetComplexToDerived : TargetComplex → TargetDerived)
  (pushforwardComplex : SourceComplex → TargetComplex)
  (sourceTensorComplex : SourceComplex → SourceComplex → SourceComplex)
  (pushforwardTensorComplex : SourceComplex → SourceComplex → TargetComplex)
  (targetTensorCounit :
    ∀ (K M : SourceComplex),
      ((tensorTarget.obj (targetComplexToDerived (pushforwardComplex M))).obj
        (targetComplexToDerived (pushforwardComplex K))) ⟶
          targetComplexToDerived (pushforwardTensorComplex K M))
  (pushforwardUnit :
    ∀ (K : SourceComplex),
      targetComplexToDerived (pushforwardComplex K) ⟶
        rightDerivedPushforward.obj (sourceComplexToDerived K))
  (naiveCupProduct :
    ∀ (K M : SourceComplex),
      targetComplexToDerived (pushforwardTensorComplex K M) ⟶
        targetComplexToDerived (pushforwardComplex (sourceTensorComplex K M)))
  (sourceTensorCounit :
    ∀ (K M : SourceComplex),
      ((tensorSource.obj (sourceComplexToDerived M)).obj
        (sourceComplexToDerived K)) ⟶
          sourceComplexToDerived (sourceTensorComplex K M))

namespace DerivedPushforwardTensorNaiveCup

/-- The tensor of the two comparison maps into the right-adjoint images. -/
abbrev top
    (K M : SourceComplex) :
    ((tensorTarget.obj (targetComplexToDerived (pushforwardComplex M))).obj
      (targetComplexToDerived (pushforwardComplex K))) ⟶
      ((tensorTarget.obj (rightDerivedPushforward.obj (sourceComplexToDerived M))).obj
        (rightDerivedPushforward.obj (sourceComplexToDerived K))) :=
  ((tensorTarget.map (pushforwardUnit M)).app
      (targetComplexToDerived (pushforwardComplex K))) ≫
    ((tensorTarget.obj (rightDerivedPushforward.obj (sourceComplexToDerived M))).map
      (pushforwardUnit K))

/-- The concrete tensor/naive-cup-product edge. -/
abbrev left
    (K M : SourceComplex) :
    ((tensorTarget.obj (targetComplexToDerived (pushforwardComplex M))).obj
      (targetComplexToDerived (pushforwardComplex K))) ⟶
      targetComplexToDerived (pushforwardComplex (sourceTensorComplex K M)) :=
  targetTensorCounit K M ≫ naiveCupProduct K M

/-- The relative cup-product edge followed by the source tensor comparison. -/
abbrev right
    (K M : SourceComplex) :
    ((tensorTarget.obj (rightDerivedPushforward.obj (sourceComplexToDerived M))).obj
      (rightDerivedPushforward.obj (sourceComplexToDerived K))) ⟶
      rightDerivedPushforward.obj (sourceComplexToDerived (sourceTensorComplex K M)) :=
  pullPushAdj.rightAdjointTensorMapOf tensorTarget tensorSource
      (fun A B ↦ (pullbackTensorIso B A).hom)
      (sourceComplexToDerived M) (sourceComplexToDerived K) ≫
    rightDerivedPushforward.map (sourceTensorCounit K M)

/-- The comparison map on the concrete tensor representative. -/
abbrev bottom
    (K M : SourceComplex) :
    targetComplexToDerived (pushforwardComplex (sourceTensorComplex K M)) ⟶
      rightDerivedPushforward.obj (sourceComplexToDerived (sourceTensorComplex K M)) :=
  pushforwardUnit (sourceTensorComplex K M)

end DerivedPushforwardTensorNaiveCup

/-- The tensor/naive-cup-product square commutes when its pullback-side transpose commutes.
The four representative-level maps remain explicit so this bridge applies to any concrete model
of complexes and does not impose a hidden choice of derived-category representatives. -/
@[stacks 0FPK "tensor and naive cup-product comparison"]
theorem derivedPushforward_tensor_naiveCupProduct_commSq
    (pullbackCounit :
      ∀ K : SourceComplex,
        leftDerivedPullback.obj (targetComplexToDerived (pushforwardComplex K)) ⟶
          sourceComplexToDerived K)
    (pullbackCounit_spec :
      ∀ K : SourceComplex,
        ((pullPushAdj.homEquiv
            (targetComplexToDerived (pushforwardComplex K))
            (sourceComplexToDerived K)).symm
          (pushforwardUnit K)) =
          pullbackCounit K)
    (pullbackCompatibility :
      ∀ K M : SourceComplex,
        CommSq
          (leftDerivedPullback.map
            (((tensorTarget.map (pushforwardUnit M)).app
                (targetComplexToDerived (pushforwardComplex K))) ≫
              ((tensorTarget.obj (rightDerivedPushforward.obj (sourceComplexToDerived M))).map
                (pushforwardUnit K))))
          (leftDerivedPullback.map (targetTensorCounit K M ≫ naiveCupProduct K M))
          (pullPushAdj.rightAdjointTensorMapAdjointOf tensorTarget tensorSource
              (fun A B ↦ (pullbackTensorIso B A).hom)
              (sourceComplexToDerived M) (sourceComplexToDerived K) ≫
            sourceTensorCounit K M)
          (pullbackCounit (sourceTensorComplex K M)))
    (K M : SourceComplex) :
    CommSq
      (((tensorTarget.map (pushforwardUnit M)).app
          (targetComplexToDerived (pushforwardComplex K))) ≫
        ((tensorTarget.obj (rightDerivedPushforward.obj (sourceComplexToDerived M))).map
          (pushforwardUnit K)))
      (targetTensorCounit K M ≫ naiveCupProduct K M)
      (pullPushAdj.rightAdjointTensorMapOf tensorTarget tensorSource
          (fun A B ↦ (pullbackTensorIso B A).hom)
          (sourceComplexToDerived M) (sourceComplexToDerived K) ≫
        rightDerivedPushforward.map (sourceTensorCounit K M))
      (pushforwardUnit (sourceTensorComplex K M)) := sorry

/- The source-side hypothesis is often already available as the mate of the comparison map.  In
that situation the counit witness used by the legacy bridge above is redundant. -/
/-- The tensor/naive-cup-product square from its mate square.

This is the preferred downstream interface: the compatibility condition is stated directly with
the adjunction transpose of the bottom edge, so applications do not have to manufacture a second
`pullbackCounit` family together with a pointwise specification theorem. -/
@[stacks 0FPK "tensor and naive cup-product comparison, mate form"]
theorem DerivedPushforwardTensorNaiveCup.commSqOfMate
    (mate :
      ∀ K M : SourceComplex,
        CommSq
          (leftDerivedPullback.map
            (DerivedPushforwardTensorNaiveCup.top
              tensorTarget sourceComplexToDerived targetComplexToDerived pushforwardComplex
              pushforwardUnit K M))
          (leftDerivedPullback.map
            (DerivedPushforwardTensorNaiveCup.left
              tensorTarget targetComplexToDerived pushforwardComplex sourceTensorComplex
              pushforwardTensorComplex targetTensorCounit naiveCupProduct K M))
          (pullPushAdj.rightAdjointTensorMapAdjointOf tensorTarget tensorSource
              (fun A B ↦ (pullbackTensorIso B A).hom)
              (sourceComplexToDerived M) (sourceComplexToDerived K) ≫
            sourceTensorCounit K M)
          ((pullPushAdj.homEquiv
              (targetComplexToDerived
                (pushforwardComplex (sourceTensorComplex K M)))
              (sourceComplexToDerived (sourceTensorComplex K M))).symm
            (pushforwardUnit (sourceTensorComplex K M))))
    (K M : SourceComplex) :
    CommSq
      (DerivedPushforwardTensorNaiveCup.top
        tensorTarget sourceComplexToDerived targetComplexToDerived pushforwardComplex
        pushforwardUnit K M)
      (DerivedPushforwardTensorNaiveCup.left
        tensorTarget targetComplexToDerived pushforwardComplex sourceTensorComplex
        pushforwardTensorComplex targetTensorCounit naiveCupProduct K M)
      (DerivedPushforwardTensorNaiveCup.right
        pullPushAdj tensorSource tensorTarget pullbackTensorIso sourceComplexToDerived
        sourceTensorComplex sourceTensorCounit K M)
      (DerivedPushforwardTensorNaiveCup.bottom
        sourceComplexToDerived targetComplexToDerived pushforwardComplex sourceTensorComplex
        pushforwardUnit K M) := sorry

end CategoryTheory
