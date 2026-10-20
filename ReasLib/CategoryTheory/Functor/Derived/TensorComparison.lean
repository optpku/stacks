module

public import Mathlib.CategoryTheory.Localization.Prod
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Left
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Left
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor comparisons between left-derived functors

This file isolates the formal derived-functor argument behind preservation of a two-variable
operation.  A lax comparison on the source categories is derived in the opposite direction.
An invertible raw tensorator is accepted as an isomorphism, and the primary comparison uses only
the universal property of the target iterated model.  Direct total-derived models and their
comparison maps remain available separately for model computations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe vHY vHX vDY vDX uHY uHX uDY uDX

namespace CategoryTheory.Functor.LeftDerived.TensorComparison

variable {HY : Type uHY} {HX : Type uHX} {DY : Type uDY} {DX : Type uDX}
variable [Category.{vHY} HY] [Category.{vHX} HX]
variable [Category.{vDY} DY] [Category.{vDX} DX]

variable (LY : HY ⥤ DY) (LX : HX ⥤ DX)
variable (P : HY ⥤ HX) (LP : DY ⥤ DX)
variable (TY₀ : HY × HY ⥤ HY) (TX₀ : HX × HX ⥤ HX)
variable (TY : DY × DY ⥤ DY) (TX : DX × DX ⥤ DX)

/-- Applying the derived model of `P` in both variables has the product of the two
left-derived counits as its canonical comparison to the underived pair. -/
def pairCounit
    (εP : LY ⋙ LP ⟶ P ⋙ LX) :
    LY.prod LY ⋙ LP.prod LP ⟶ P.prod P ⋙ LX.prod LX :=
  NatTrans.prod εP εP

/-- The product counit acts componentwise in the two variables. -/
@[simp]
theorem pairCounit_app
    (εP : LY ⋙ LP ⟶ P ⋙ LX) (X : HY × HY) :
    (pairCounit LY LX P LP εP).app X =
      Prod.mkHom (εP.app X.1) (εP.app X.2) := rfl

/-- The raw functor obtained by tensoring first and then applying `P`. -/
abbrev sourceRaw : HY × HY ⥤ DX :=
  TY₀ ⋙ (P ⋙ LX)

/-- The raw functor obtained by applying `P` in both variables and then tensoring. -/
abbrev targetRaw : HY × HY ⥤ DX :=
  P.prod P ⋙ (TX₀ ⋙ LX)

/-- The lax tensor comparison, postcomposed with the target localization and reassociated to
the raw functors used by total left derivation. -/
def rawComparison
    (τ : P.prod P ⋙ TX₀ ⟶ TY₀ ⋙ P) :
    targetRaw LX P TX₀ ⟶ sourceRaw LX P TY₀ :=
  (associator (P.prod P) TX₀ LX).inv ≫
    whiskerRight τ LX ≫
    (associator TY₀ P LX).hom

/-- Reassociation and right whiskering transport an invertible raw tensorator to an
isomorphism between the two raw composite functors. -/
@[stacks 0FPH "invertible raw tensor comparison"]
def rawComparisonIso
    (τ : P.prod P ⋙ TX₀ ≅ TY₀ ⋙ P) :
    targetRaw LX P TX₀ ≅ sourceRaw LX P TY₀ :=
  (associator (P.prod P) TX₀ LX).symm ≪≫
    Functor.isoWhiskerRight τ LX ≪≫
    associator TY₀ P LX

set_option backward.isDefEq.respectTransparency false in
/-- Reassociation does not change the component of the lax raw comparison. -/
@[simp]
theorem rawComparison_app
    (τ : P.prod P ⋙ TX₀ ⟶ TY₀ ⋙ P) (X : HY × HY) :
    (rawComparison LX P TY₀ TX₀ τ).app X = LX.map (τ.app X) := by
  simp [rawComparison]

/-- The counit of the model which first derives the two-variable source operation and then
derives `P`. -/
def sourceCounit
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTY : LY.prod LY ⋙ TY ⟶ TY₀ ⋙ LY) :
    LY.prod LY ⋙ (TY ⋙ LP) ⟶ sourceRaw LX P TY₀ :=
  LeftDerived.Composition.iteratedCounit εTY εP

/-- The source-model counit first applies the derived-operation counit and then the derived
functor counit. -/
@[simp]
theorem sourceCounit_app
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTY : LY.prod LY ⋙ TY ⟶ TY₀ ⋙ LY)
    (X : HY × HY) :
    (sourceCounit LY LX P LP TY₀ TY εP εTY).app X =
      LP.map (εTY.app X) ≫ εP.app (TY₀.obj X) :=
  LeftDerived.Composition.iteratedCounit_app εTY εP X

/-- The counit of the model which derives `P` in both variables and then derives the target
two-variable operation. -/
def targetCounit
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTX : LX.prod LX ⋙ TX ⟶ TX₀ ⋙ LX) :
    LY.prod LY ⋙ (LP.prod LP ⋙ TX) ⟶ targetRaw LX P TX₀ :=
  LeftDerived.Composition.iteratedCounit (pairCounit LY LX P LP εP) εTX

/-- The target-model counit tensors the two derived-functor counits and then applies the
derived-operation counit. -/
@[simp]
theorem targetCounit_app
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTX : LX.prod LX ⋙ TX ⟶ TX₀ ⋙ LX)
    (X : HY × HY) :
    (targetCounit LY LX P LP TX₀ TX εP εTX).app X =
      TX.map (Prod.mkHom (εP.app X.1) (εP.app X.2)) ≫
        εTX.app ((P.prod P).obj X) := by
  rw [targetCounit, LeftDerived.Composition.iteratedCounit_app, pairCounit_app]
  rfl

/-- A natural transformation between the two iterated derived models is a tensor comparison
when it identifies their counits through the inverse raw tensorator.  This predicate is the
model-independent specification used to recognize concrete constructions. -/
@[stacks 0FPH "left-derived tensor comparison specification"]
def IsComparison
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTY : LY.prod LY ⋙ TY ⟶ TY₀ ⋙ LY)
    (εTX : LX.prod LX ⋙ TX ⟶ TX₀ ⋙ LX)
    (τ : P.prod P ⋙ TX₀ ≅ TY₀ ⋙ P)
    (φ : TY ⋙ LP ⟶ LP.prod LP ⋙ TX) : Prop :=
  whiskerLeft (LY.prod LY) φ ≫
      targetCounit LY LX P LP TX₀ TX εP εTX =
    sourceCounit LY LX P LP TY₀ TY εP εTY ≫
      (rawComparisonIso LX P TY₀ TX₀ τ).inv

variable (W : MorphismProperty (HY × HY))
variable [LY.prod LY |>.IsLocalization W]

section DirectModels

variable [(sourceRaw LX P TY₀).HasLeftDerivedFunctor W]
variable [(targetRaw LX P TX₀).HasLeftDerivedFunctor W]

/-- The total left derived functor of tensoring first and then applying `P`. -/
noncomputable abbrev sourceDerived : DY × DY ⥤ DX :=
  (sourceRaw LX P TY₀).totalLeftDerived (LY.prod LY) W

/-- The total left derived functor of applying `P` twice and then tensoring. -/
noncomputable abbrev targetDerived : DY × DY ⥤ DX :=
  (targetRaw LX P TX₀).totalLeftDerived (LY.prod LY) W

/-- The canonical map from the iterated source model to the direct total left-derived
functor. -/
noncomputable def sourceComparison
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTY : LY.prod LY ⋙ TY ⟶ TY₀ ⋙ LY) :
    TY ⋙ LP ⟶ sourceDerived LY LX P TY₀ W :=
  LeftDerived.Composition.comparisonOfModels W εTY εP
    ((sourceRaw LX P TY₀).totalLeftDerivedCounit (LY.prod LY) W)

/-- The canonical map from the iterated target model to the direct total left-derived
functor. -/
noncomputable def targetComparison
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTX : LX.prod LX ⋙ TX ⟶ TX₀ ⋙ LX) :
    LP.prod LP ⋙ TX ⟶ targetDerived LY LX P TX₀ W :=
  LeftDerived.Composition.comparisonOfModels W
    (pairCounit LY LX P LP εP) εTX
    ((targetRaw LX P TX₀).totalLeftDerivedCounit (LY.prod LY) W)

/-- Deriving the inverse raw tensor comparison gives a comparison between the two direct
total left-derived functors. -/
noncomputable def directComparison
    (τ : P.prod P ⋙ TX₀ ≅ TY₀ ⋙ P) :
    sourceDerived LY LX P TY₀ W ⟶ targetDerived LY LX P TX₀ W :=
  LeftDerived.mapNatTrans (LY.prod LY) W
    (rawComparisonIso LX P TY₀ TX₀ τ).inv

end DirectModels

/-- The derived tensor-preservation comparison in the source-facing direction.  Only the raw
tensorator is inverted; the target iterated model supplies the universal property. -/
@[stacks 0FPH "left-derived tensor comparison"]
noncomputable def comparison
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTY : LY.prod LY ⋙ TY ⟶ TY₀ ⋙ LY)
    (εTX : LX.prod LX ⋙ TX ⟶ TX₀ ⋙ LX)
    (τ : P.prod P ⋙ TX₀ ≅ TY₀ ⋙ P)
    [(LP.prod LP ⋙ TX).IsLeftDerivedFunctor
      (targetCounit LY LX P LP TX₀ TX εP εTX) W] :
    TY ⋙ LP ⟶ LP.prod LP ⋙ TX :=
  Functor.leftDerivedNatTrans
    (TY ⋙ LP) (LP.prod LP ⋙ TX)
    (sourceCounit LY LX P LP TY₀ TY εP εTY)
    (targetCounit LY LX P LP TX₀ TX εP εTX) W
    (rawComparisonIso LX P TY₀ TX₀ τ).inv

/-- `0FPH:` The forward derived tensor comparison from an explicit target-model certificate. -/
@[stacks 0FPH "left-derived tensor comparison from an explicit target model"]
noncomputable def comparisonOf
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTY : LY.prod LY ⋙ TY ⟶ TY₀ ⋙ LY)
    (εTX : LX.prod LX ⋙ TX ⟶ TX₀ ⋙ LX)
    (τ : P.prod P ⋙ TX₀ ≅ TY₀ ⋙ P)
    (hTarget : (LP.prod LP ⋙ TX).IsLeftDerivedFunctor
      (targetCounit LY LX P LP TX₀ TX εP εTX) W) :
    TY ⋙ LP ⟶ LP.prod LP ⋙ TX :=
  @comparison HY HX DY DX _ _ _ _ LY LX P LP TY₀ TX₀ TY TX W _
    εP εTY εTX τ hTarget

/-- `0FPH:` The explicit forward comparison satisfies the target-model counit equation. -/
@[stacks 0FPH "explicit left-derived tensor comparison counit"]
theorem comparisonOf_counit
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTY : LY.prod LY ⋙ TY ⟶ TY₀ ⋙ LY)
    (εTX : LX.prod LX ⋙ TX ⟶ TX₀ ⋙ LX)
    (τ : P.prod P ⋙ TX₀ ≅ TY₀ ⋙ P)
    (hTarget : (LP.prod LP ⋙ TX).IsLeftDerivedFunctor
      (targetCounit LY LX P LP TX₀ TX εP εTX) W) :
    whiskerLeft (LY.prod LY)
        (comparisonOf LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ hTarget) ≫
      targetCounit LY LX P LP TX₀ TX εP εTX =
        sourceCounit LY LX P LP TY₀ TY εP εTY ≫
          (rawComparisonIso LX P TY₀ TX₀ τ).inv := by
  letI := hTarget
  exact Functor.leftDerivedNatTrans_fac
    (TY ⋙ LP) (LP.prod LP ⋙ TX)
    (sourceCounit LY LX P LP TY₀ TY εP εTY)
    (targetCounit LY LX P LP TX₀ TX εP εTX) W
    (rawComparisonIso LX P TY₀ TX₀ τ).inv

/-- `0FPH:` The explicit forward comparison satisfies its defining tensor-comparison predicate. -/
@[stacks 0FPH "explicit left-derived tensor comparison specification"]
theorem comparisonOf_isComparison
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTY : LY.prod LY ⋙ TY ⟶ TY₀ ⋙ LY)
    (εTX : LX.prod LX ⋙ TX ⟶ TX₀ ⋙ LX)
    (τ : P.prod P ⋙ TX₀ ≅ TY₀ ⋙ P)
    (hTarget : (LP.prod LP ⋙ TX).IsLeftDerivedFunctor
      (targetCounit LY LX P LP TX₀ TX εP εTX) W) :
    IsComparison LY LX P LP TY₀ TX₀ TY TX εP εTY εTX τ
      (comparisonOf LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ hTarget) := by
  exact comparisonOf_counit LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ hTarget

/-- `0FPH:` The reverse derived tensor comparison, constructed from the source iterated model and
the forward raw tensorator. -/
@[stacks 0FPH "reverse left-derived tensor comparison"]
noncomputable def comparisonInv
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTY : LY.prod LY ⋙ TY ⟶ TY₀ ⋙ LY)
    (εTX : LX.prod LX ⋙ TX ⟶ TX₀ ⋙ LX)
    (τ : P.prod P ⋙ TX₀ ≅ TY₀ ⋙ P)
    [(TY ⋙ LP).IsLeftDerivedFunctor
      (sourceCounit LY LX P LP TY₀ TY εP εTY) W] :
    LP.prod LP ⋙ TX ⟶ TY ⋙ LP :=
  Functor.leftDerivedNatTrans
    (LP.prod LP ⋙ TX) (TY ⋙ LP)
    (targetCounit LY LX P LP TX₀ TX εP εTX)
    (sourceCounit LY LX P LP TY₀ TY εP εTY) W
    (rawComparisonIso LX P TY₀ TX₀ τ).hom

/-- `0FPH:` The reverse derived tensor comparison from an explicit source-model certificate. -/
@[stacks 0FPH "reverse left-derived tensor comparison from an explicit source model"]
noncomputable def comparisonInvOf
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTY : LY.prod LY ⋙ TY ⟶ TY₀ ⋙ LY)
    (εTX : LX.prod LX ⋙ TX ⟶ TX₀ ⋙ LX)
    (τ : P.prod P ⋙ TX₀ ≅ TY₀ ⋙ P)
    (hSource : (TY ⋙ LP).IsLeftDerivedFunctor
      (sourceCounit LY LX P LP TY₀ TY εP εTY) W) :
    LP.prod LP ⋙ TX ⟶ TY ⋙ LP :=
  @comparisonInv HY HX DY DX _ _ _ _ LY LX P LP TY₀ TX₀ TY TX W _
    εP εTY εTX τ hSource

/-- `0FPH:` The explicit reverse comparison satisfies the source-facing counit equation. -/
@[stacks 0FPH "explicit reverse left-derived tensor comparison counit"]
theorem comparisonInvOf_counit
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTY : LY.prod LY ⋙ TY ⟶ TY₀ ⋙ LY)
    (εTX : LX.prod LX ⋙ TX ⟶ TX₀ ⋙ LX)
    (τ : P.prod P ⋙ TX₀ ≅ TY₀ ⋙ P)
    (hSource : (TY ⋙ LP).IsLeftDerivedFunctor
      (sourceCounit LY LX P LP TY₀ TY εP εTY) W) :
    whiskerLeft (LY.prod LY)
        (comparisonInvOf LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ hSource) ≫
      sourceCounit LY LX P LP TY₀ TY εP εTY =
        targetCounit LY LX P LP TX₀ TX εP εTX ≫
          (rawComparisonIso LX P TY₀ TX₀ τ).hom := by
  letI := hSource
  exact Functor.leftDerivedNatTrans_fac
    (LP.prod LP ⋙ TX) (TY ⋙ LP)
    (targetCounit LY LX P LP TX₀ TX εP εTX)
    (sourceCounit LY LX P LP TY₀ TY εP εTY) W
    (rawComparisonIso LX P TY₀ TX₀ τ).hom

/-- `0FPH:` The canonical reverse comparison satisfies the source-facing counit equation. -/
@[stacks 0FPH "canonical reverse left-derived tensor comparison counit"]
theorem comparisonInv_counit
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTY : LY.prod LY ⋙ TY ⟶ TY₀ ⋙ LY)
    (εTX : LX.prod LX ⋙ TX ⟶ TX₀ ⋙ LX)
    (τ : P.prod P ⋙ TX₀ ≅ TY₀ ⋙ P)
    [(TY ⋙ LP).IsLeftDerivedFunctor
      (sourceCounit LY LX P LP TY₀ TY εP εTY) W] :
    whiskerLeft (LY.prod LY)
        (comparisonInv LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ) ≫
      sourceCounit LY LX P LP TY₀ TY εP εTY =
        targetCounit LY LX P LP TX₀ TX εP εTX ≫
          (rawComparisonIso LX P TY₀ TX₀ τ).hom := by
  exact Functor.leftDerivedNatTrans_fac
    (LP.prod LP ⋙ TX) (TY ⋙ LP)
    (targetCounit LY LX P LP TX₀ TX εP εTX)
    (sourceCounit LY LX P LP TY₀ TY εP εTY) W
    (rawComparisonIso LX P TY₀ TX₀ τ).hom

/-- `0FPH:` The derived tensor comparison followed by its explicit reverse is the identity. -/
@[stacks 0FPH "left-derived tensor comparison hom-inv law"]
theorem comparison_comp_comparisonInv
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTY : LY.prod LY ⋙ TY ⟶ TY₀ ⋙ LY)
    (εTX : LX.prod LX ⋙ TX ⟶ TX₀ ⋙ LX)
    (τ : P.prod P ⋙ TX₀ ≅ TY₀ ⋙ P)
    [(TY ⋙ LP).IsLeftDerivedFunctor
      (sourceCounit LY LX P LP TY₀ TY εP εTY) W]
    [(LP.prod LP ⋙ TX).IsLeftDerivedFunctor
      (targetCounit LY LX P LP TX₀ TX εP εTX) W] :
    comparison LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ ≫
      comparisonInv LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ = 𝟙 _ := by
  change Functor.leftDerivedNatTrans
      (TY ⋙ LP) (LP.prod LP ⋙ TX)
        (sourceCounit LY LX P LP TY₀ TY εP εTY)
        (targetCounit LY LX P LP TX₀ TX εP εTX) W
        (rawComparisonIso LX P TY₀ TX₀ τ).inv ≫
      Functor.leftDerivedNatTrans
        (LP.prod LP ⋙ TX) (TY ⋙ LP)
        (targetCounit LY LX P LP TX₀ TX εP εTX)
        (sourceCounit LY LX P LP TY₀ TY εP εTY) W
        (rawComparisonIso LX P TY₀ TX₀ τ).hom = 𝟙 _
  rw [Functor.leftDerivedNatTrans_comp]
  simp

/-- `0FPH:` The explicit reverse followed by the derived tensor comparison is the identity. -/
@[stacks 0FPH "left-derived tensor comparison inv-hom law"]
theorem comparisonInv_comp_comparison
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTY : LY.prod LY ⋙ TY ⟶ TY₀ ⋙ LY)
    (εTX : LX.prod LX ⋙ TX ⟶ TX₀ ⋙ LX)
    (τ : P.prod P ⋙ TX₀ ≅ TY₀ ⋙ P)
    [(TY ⋙ LP).IsLeftDerivedFunctor
      (sourceCounit LY LX P LP TY₀ TY εP εTY) W]
    [(LP.prod LP ⋙ TX).IsLeftDerivedFunctor
      (targetCounit LY LX P LP TX₀ TX εP εTX) W] :
    comparisonInv LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ ≫
      comparison LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ = 𝟙 _ := by
  change Functor.leftDerivedNatTrans
      (LP.prod LP ⋙ TX) (TY ⋙ LP)
        (targetCounit LY LX P LP TX₀ TX εP εTX)
        (sourceCounit LY LX P LP TY₀ TY εP εTY) W
        (rawComparisonIso LX P TY₀ TX₀ τ).hom ≫
      Functor.leftDerivedNatTrans
        (TY ⋙ LP) (LP.prod LP ⋙ TX)
        (sourceCounit LY LX P LP TY₀ TY εP εTY)
        (targetCounit LY LX P LP TX₀ TX εP εTX) W
        (rawComparisonIso LX P TY₀ TX₀ τ).inv = 𝟙 _
  rw [Functor.leftDerivedNatTrans_comp]
  simp

/-- `0FPH:` The derived tensor comparison as an isomorphism with explicit forward and reverse
natural transformations. -/
@[stacks 0FPH "left-derived tensor comparison isomorphism"]
noncomputable def comparisonIso
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTY : LY.prod LY ⋙ TY ⟶ TY₀ ⋙ LY)
    (εTX : LX.prod LX ⋙ TX ⟶ TX₀ ⋙ LX)
    (τ : P.prod P ⋙ TX₀ ≅ TY₀ ⋙ P)
    [(TY ⋙ LP).IsLeftDerivedFunctor
      (sourceCounit LY LX P LP TY₀ TY εP εTY) W]
    [(LP.prod LP ⋙ TX).IsLeftDerivedFunctor
      (targetCounit LY LX P LP TX₀ TX εP εTX) W] :
    TY ⋙ LP ≅ LP.prod LP ⋙ TX where
  hom := comparison LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ
  inv := comparisonInv LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ
  hom_inv_id := comparison_comp_comparisonInv LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ
  inv_hom_id := comparisonInv_comp_comparison LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ

/-- `0FPH:` The derived tensor comparison isomorphism from explicit source- and target-model
certificates. -/
@[stacks 0FPH "left-derived tensor comparison isomorphism from explicit models"]
noncomputable def comparisonIsoOf
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTY : LY.prod LY ⋙ TY ⟶ TY₀ ⋙ LY)
    (εTX : LX.prod LX ⋙ TX ⟶ TX₀ ⋙ LX)
    (τ : P.prod P ⋙ TX₀ ≅ TY₀ ⋙ P)
    (hSource : (TY ⋙ LP).IsLeftDerivedFunctor
      (sourceCounit LY LX P LP TY₀ TY εP εTY) W)
    (hTarget : (LP.prod LP ⋙ TX).IsLeftDerivedFunctor
      (targetCounit LY LX P LP TX₀ TX εP εTX) W) :
    TY ⋙ LP ≅ LP.prod LP ⋙ TX :=
  @comparisonIso HY HX DY DX _ _ _ _ LY LX P LP TY₀ TX₀ TY TX W _
    εP εTY εTX τ hSource hTarget

/-- `0FPH:` The forward map of the explicit derived tensor comparison isomorphism. -/
@[simp, stacks 0FPH "explicit left-derived tensor comparison isomorphism hom"]
theorem comparisonIsoOf_hom
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTY : LY.prod LY ⋙ TY ⟶ TY₀ ⋙ LY)
    (εTX : LX.prod LX ⋙ TX ⟶ TX₀ ⋙ LX)
    (τ : P.prod P ⋙ TX₀ ≅ TY₀ ⋙ P)
    (hSource : (TY ⋙ LP).IsLeftDerivedFunctor
      (sourceCounit LY LX P LP TY₀ TY εP εTY) W)
    (hTarget : (LP.prod LP ⋙ TX).IsLeftDerivedFunctor
      (targetCounit LY LX P LP TX₀ TX εP εTX) W) :
    (comparisonIsoOf LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ hSource hTarget).hom =
      comparisonOf LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ hTarget := rfl

/-- `0FPH:` The reverse map of the explicit derived tensor comparison isomorphism. -/
@[simp, stacks 0FPH "explicit left-derived tensor comparison isomorphism inv"]
theorem comparisonIsoOf_inv
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTY : LY.prod LY ⋙ TY ⟶ TY₀ ⋙ LY)
    (εTX : LX.prod LX ⋙ TX ⟶ TX₀ ⋙ LX)
    (τ : P.prod P ⋙ TX₀ ≅ TY₀ ⋙ P)
    (hSource : (TY ⋙ LP).IsLeftDerivedFunctor
      (sourceCounit LY LX P LP TY₀ TY εP εTY) W)
    (hTarget : (LP.prod LP ⋙ TX).IsLeftDerivedFunctor
      (targetCounit LY LX P LP TX₀ TX εP εTX) W) :
    (comparisonIsoOf LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ hSource hTarget).inv =
      comparisonInvOf LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ hSource := rfl

/-- `0FPH:` The forward map of the canonical derived tensor comparison isomorphism. -/
@[simp, stacks 0FPH "canonical left-derived tensor comparison isomorphism hom"]
theorem comparisonIso_hom
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTY : LY.prod LY ⋙ TY ⟶ TY₀ ⋙ LY)
    (εTX : LX.prod LX ⋙ TX ⟶ TX₀ ⋙ LX)
    (τ : P.prod P ⋙ TX₀ ≅ TY₀ ⋙ P)
    [(TY ⋙ LP).IsLeftDerivedFunctor
      (sourceCounit LY LX P LP TY₀ TY εP εTY) W]
    [(LP.prod LP ⋙ TX).IsLeftDerivedFunctor
      (targetCounit LY LX P LP TX₀ TX εP εTX) W] :
    (comparisonIso LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ).hom =
      comparison LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ := rfl

/-- `0FPH:` The reverse map of the canonical derived tensor comparison isomorphism. -/
@[simp, stacks 0FPH "canonical left-derived tensor comparison isomorphism inv"]
theorem comparisonIso_inv
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTY : LY.prod LY ⋙ TY ⟶ TY₀ ⋙ LY)
    (εTX : LX.prod LX ⋙ TX ⟶ TX₀ ⋙ LX)
    (τ : P.prod P ⋙ TX₀ ≅ TY₀ ⋙ P)
    [(TY ⋙ LP).IsLeftDerivedFunctor
      (sourceCounit LY LX P LP TY₀ TY εP εTY) W]
    [(LP.prod LP ⋙ TX).IsLeftDerivedFunctor
      (targetCounit LY LX P LP TX₀ TX εP εTX) W] :
    (comparisonIso LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ).inv =
      comparisonInv LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ := rfl

/-- The canonical left-derived tensor comparison satisfies its defining counit equation. -/
@[stacks 0FPH "canonical left-derived tensor comparison specification"]
theorem comparison_isComparison
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTY : LY.prod LY ⋙ TY ⟶ TY₀ ⋙ LY)
    (εTX : LX.prod LX ⋙ TX ⟶ TX₀ ⋙ LX)
    (τ : P.prod P ⋙ TX₀ ≅ TY₀ ⋙ P)
    [(LP.prod LP ⋙ TX).IsLeftDerivedFunctor
      (targetCounit LY LX P LP TX₀ TX εP εTX) W] :
    IsComparison LY LX P LP TY₀ TX₀ TY TX εP εTY εTX τ
      (comparison LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ) := by
  exact comparisonOf_isComparison LY LX P LP TY₀ TX₀ TY TX W
    εP εTY εTX τ inferInstance

/-- A candidate satisfying the tensor-comparison counit equation equals the canonical comparison
provided by the target left-derived model. -/
@[stacks 0FPH "uniqueness of left-derived tensor comparison"]
theorem IsComparison.eq_comparison
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTY : LY.prod LY ⋙ TY ⟶ TY₀ ⋙ LY)
    (εTX : LX.prod LX ⋙ TX ⟶ TX₀ ⋙ LX)
    (τ : P.prod P ⋙ TX₀ ≅ TY₀ ⋙ P)
    [hTX : (LP.prod LP ⋙ TX).IsLeftDerivedFunctor
      (targetCounit LY LX P LP TX₀ TX εP εTX) W]
    {φ : TY ⋙ LP ⟶ LP.prod LP ⋙ TX}
    (hφ : IsComparison LY LX P LP TY₀ TX₀ TY TX εP εTY εTX τ φ) :
    φ = comparison LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ := by
  apply Functor.leftDerived_ext
    (LP.prod LP ⋙ TX) (targetCounit LY LX P LP TX₀ TX εP εTX) W
  exact hφ.trans
    (comparisonOf_counit LY LX P LP TY₀ TX₀ TY TX W
      εP εTY εTX τ hTX).symm

/-- The derived tensor comparison is characterized by the two iterated counits and the inverse
raw tensor comparison. -/
@[stacks 0FPH "derived tensor comparison counit"]
theorem comparison_counit
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTY : LY.prod LY ⋙ TY ⟶ TY₀ ⋙ LY)
    (εTX : LX.prod LX ⋙ TX ⟶ TX₀ ⋙ LX)
    (τ : P.prod P ⋙ TX₀ ≅ TY₀ ⋙ P)
    [(LP.prod LP ⋙ TX).IsLeftDerivedFunctor
      (targetCounit LY LX P LP TX₀ TX εP εTX) W] :
    whiskerLeft (LY.prod LY)
        (comparison LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ) ≫
      targetCounit LY LX P LP TX₀ TX εP εTX =
        sourceCounit LY LX P LP TY₀ TY εP εTY ≫
          (rawComparisonIso LX P TY₀ TX₀ τ).inv := by
  exact Functor.leftDerivedNatTrans_fac
    (TY ⋙ LP) (LP.prod LP ⋙ TX)
    (sourceCounit LY LX P LP TY₀ TY εP εTY)
    (targetCounit LY LX P LP TX₀ TX εP εTX) W
    (rawComparisonIso LX P TY₀ TX₀ τ).inv

/-- Pointwise form of `comparison_counit`, displaying the outer boundary of the six-object
derived tensor diagram. -/
@[stacks 0FPH "derived tensor comparison counit component"]
theorem comparison_counit_app
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTY : LY.prod LY ⋙ TY ⟶ TY₀ ⋙ LY)
    (εTX : LX.prod LX ⋙ TX ⟶ TX₀ ⋙ LX)
    (τ : P.prod P ⋙ TX₀ ≅ TY₀ ⋙ P)
    [(LP.prod LP ⋙ TX).IsLeftDerivedFunctor
      (targetCounit LY LX P LP TX₀ TX εP εTX) W]
    (X : HY × HY) :
    (comparison LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ).app
          ((LY.prod LY).obj X) ≫
        (targetCounit LY LX P LP TX₀ TX εP εTX).app X =
      (sourceCounit LY LX P LP TY₀ TY εP εTY).app X ≫
        (rawComparisonIso LX P TY₀ TX₀ τ).inv.app X := by
  exact NatTrans.congr_app
    (comparison_counit LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ) X

/-- If the source iterated model also satisfies the left-derived universal property, then the
derived tensor-preservation comparison is invertible. -/
theorem comparison_isIso
    (εP : LY ⋙ LP ⟶ P ⋙ LX)
    (εTY : LY.prod LY ⋙ TY ⟶ TY₀ ⋙ LY)
    (εTX : LX.prod LX ⋙ TX ⟶ TX₀ ⋙ LX)
    (τ : P.prod P ⋙ TX₀ ≅ TY₀ ⋙ P)
    [(TY ⋙ LP).IsLeftDerivedFunctor
      (sourceCounit LY LX P LP TY₀ TY εP εTY) W]
    [(LP.prod LP ⋙ TX).IsLeftDerivedFunctor
      (targetCounit LY LX P LP TX₀ TX εP εTX) W] :
    IsIso (comparison LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ) := by
  rw [← comparisonIso_hom LY LX P LP TY₀ TX₀ TY TX W εP εTY εTX τ]
  infer_instance

end CategoryTheory.Functor.LeftDerived.TensorComparison
