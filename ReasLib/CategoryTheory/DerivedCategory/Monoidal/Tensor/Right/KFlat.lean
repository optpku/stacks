/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Monoidal
public import ReasLib.Algebra.Homology.DerivedCategory.Monoidal.KFlat.Resolution
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fixed-right derived tensor models from K-flat resolutions

This leaf is the canonical bridge from a selected functorial K-flat resolution to the ambient
derived tensor product.  It supplies concrete counit components; the left-derived universal
property is a named proposition and is not inferred from monoidality alone.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.DerivedTensor.Right.KFlat

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C]
variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ C,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [HomotopyCategory.Koszul.TensorDescends (C := C)]
variable [HomotopyCategory.KFlat.TensorDescends (C := C)]
variable [DerivedCategory.KFlat.IsLocalization (C := C)]

/-- Stacks 0FPB: the homotopy representative used for a derived object. -/
@[stacks 0FPB "K-flat bridge representative"]
noncomputable abbrev representative (E : DerivedCategory C) :
    HomotopyCategory C (up ℤ) :=
  (HomotopyCategory.quotient C (up ℤ)).obj
    ((DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C).objPreimage E)

/-- Stacks 0FPB: compare a derived object with the localization of its selected K-flat
representative. -/
@[stacks 0FPB "K-flat representative comparison"]
noncomputable def representativeIso
    (P : HomotopyCategory.KFlat.ResolutionFunctor C) (E : DerivedCategory C) :
  E ≅ (DerivedCategory.KFlat.resolvedLocalization P).obj (representative E) :=
  (DerivedTensor.Right.representativeIso E).symm ≪≫
    (DerivedCategory.KFlat.resolutionObjIso P (representative E)).symm

/-- Stacks 0FPB: the objectwise ambient counit for fixed-right tensoring from a selected K-flat
resolution.  The displayed composite records the resolution, tensor, and representative maps in
the order used by downstream proofs. -/
@[stacks 0FPB "K-flat fixed-right counit component"]
noncomputable def counitApp
    (P : HomotopyCategory.KFlat.ResolutionFunctor C) (E : DerivedCategory C)
    (K : HomotopyCategory C (up ℤ)) :
    (DerivedCategory.Qh.obj K ⊗ E) ⟶
      (DerivedTensor.Right.sourceFunctor E).obj K :=
  ((DerivedCategory.KFlat.resolutionObjIso P K).inv ⊗ₘ
      (representativeIso P E).hom) ≫
    (DerivedCategory.KFlat.mapTensorIso (P.toFunctor.obj K)
        (P.toFunctor.obj (representative E))).hom ≫
    DerivedCategory.Qh.map
      ((Functor.Monoidal.μIso ((HomotopyCategory.kFlat C).ι)
          (P.toFunctor.obj K) (P.toFunctor.obj (representative E))).inv ≫
        (P.counit.app K ⊗ₘ P.counit.app (representative E))) ≫
    (DerivedTensor.Right.sourceFunctorIso E).hom.app K

/-- Stacks 0FPB: the ambient natural counit for fixed-right tensoring from a selected K-flat
resolution. -/
@[stacks 0FPB "K-flat fixed-right counit"]
noncomputable def counit
    (P : HomotopyCategory.KFlat.ResolutionFunctor C) (E : DerivedCategory C) :
    (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C) ⋙
        MonoidalCategory.tensorRight E ⟶
      DerivedTensor.Right.sourceFunctor E :=
  { app := fun K => counitApp P E K
    naturality := fun f => sorry }

/-- Stacks 0FPB: the universal-property law needed to use the K-flat ambient counit as a fixed
right derived model. -/
@[stacks 0FPB "K-flat fixed-right derived law"]
theorem counit_isLeftDerived
    (P : HomotopyCategory.KFlat.ResolutionFunctor C) (E : DerivedCategory C) :
    (MonoidalCategory.tensorRight E).IsLeftDerivedFunctor (counit P E)
      (HomotopyCategory.quasiIso C (up ℤ)) := sorry

/-- Stacks 0FPB: the fixed-right derived model supplied by a selected K-flat resolution. -/
@[stacks 0FPB "K-flat fixed-right derived model"]
noncomputable def model
    (P : HomotopyCategory.KFlat.ResolutionFunctor C) (E : DerivedCategory C) :
    DerivedTensor.Right.Model E :=
  DerivedTensor.Right.Model.of E (MonoidalCategory.tensorRight E) (counit P E)
    (counit_isLeftDerived P E)

/-- Stacks 0FPB: the ambient model family supplied by a selected K-flat resolution. -/
@[stacks 0FPB "K-flat ambient model family"]
noncomputable def modelFamily
    (P : HomotopyCategory.KFlat.ResolutionFunctor C) :
    DerivedTensor.Right.Monoidal.Model (C := C) where
  counit := counit P
  isLeftDerived := counit_isLeftDerived P

/-- Stacks 0FPB: compare canonical fixed-right derived tensoring with the K-flat ambient tensor. -/
@[stacks 0FPB "K-flat fixed-right comparison"]
noncomputable abbrev functorIsoTensorRight
    (P : HomotopyCategory.KFlat.ResolutionFunctor C) (E : DerivedCategory C)
    [DerivedTensor.Right.Has (C := C)] :
    DerivedTensor.Right.functor E ≅ MonoidalCategory.tensorRight E :=
  DerivedTensor.Right.Monoidal.Model.functorIsoTensorRight (modelFamily P) E

/-- Stacks 0FPB: compare ambient right tensoring with canonical fixed-right derivation using a
selected K-flat resolution. -/
@[stacks 0FPB "K-flat ambient tensor comparison"]
noncomputable abbrev tensorRightIsoFunctor
    (P : HomotopyCategory.KFlat.ResolutionFunctor C) (E : DerivedCategory C)
    [DerivedTensor.Right.Has (C := C)] :
    MonoidalCategory.tensorRight E ≅ DerivedTensor.Right.functor E :=
  (functorIsoTensorRight P E).symm

/-- Stacks 0FPB: the objectwise K-flat fixed-right comparison. -/
@[stacks 0FPB "K-flat fixed-right object comparison"]
noncomputable abbrev objIsoTensor
    (P : HomotopyCategory.KFlat.ResolutionFunctor C) (K E : DerivedCategory C)
    [DerivedTensor.Right.Has (C := C)] :
    DerivedTensor.Right.obj K E ≅ K ⊗ E :=
  (functorIsoTensorRight P E).app K

/-- Stacks 0FPB: objectwise comparison from the ambient tensor product to fixed-right derived
tensoring. -/
@[stacks 0FPB "K-flat ambient tensor object comparison"]
noncomputable abbrev tensorIsoObj
    (P : HomotopyCategory.KFlat.ResolutionFunctor C) (K E : DerivedCategory C)
    [DerivedTensor.Right.Has (C := C)] :
    K ⊗ E ≅ DerivedTensor.Right.obj K E :=
  (objIsoTensor P K E).symm

/-- Stacks 0FPB: the K-flat fixed-right comparison intertwines the concrete ambient counit. -/
@[reassoc (attr := simp), stacks 0FPB "K-flat fixed-right counit compatibility"]
theorem functorIsoTensorRight_counit
    (P : HomotopyCategory.KFlat.ResolutionFunctor C) (E : DerivedCategory C)
    [DerivedTensor.Right.Has (C := C)] :
    Functor.whiskerLeft (DerivedTensor.Right.localization (C := C))
        (functorIsoTensorRight P E).hom ≫ counit P E =
      DerivedTensor.Right.counit E :=
  DerivedTensor.Right.Monoidal.Model.functorIsoTensorRight_counit (modelFamily P) E

end CategoryTheory.DerivedCategory.DerivedTensor.Right.KFlat
