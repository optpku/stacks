module

public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Bifunctor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ambient tensor comparison for the derived tensor bifunctor

@stack 064M

This leaf is the two-variable bridge between the canonical derived tensor bifunctor and an
ambient tensor on the derived category.  A fixed-right model family determines the comparison
components, but not their naturality in the right tensor factor.  The latter is therefore an
explicit proposition consumed by the functor-level API.  No monoidal instance is installed and
no independently chosen tensor functors are identified by definitional equality.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Monoidal

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ C,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [HomotopyCategory.Koszul.TensorDescends (C := C)]
variable [MonoidalCategory (DerivedCategory C)]
variable [DerivedTensor.Right.Has (C := C)]

/-- `064M:` The objectwise comparison from an explicit two-variable model to an ambient tensor. -/
@[stacks 064M "derived tensor to ambient tensor object comparison"]
noncomputable def objIsoTensorOfModels
    (B : DerivedTensor.Bifunctor.Model (C := C))
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C,
      DerivedTensor.Bifunctor.Right.Model.Compatible B E)
    (X : DerivedCategory C × DerivedCategory C) :
    B.functor.obj X ≅
      (MonoidalCategory.tensor (DerivedCategory C)).obj X :=
  (DerivedTensor.Bifunctor.Right.Model.isoAppOf B X.2 (h X.2) X.1).symm ≪≫
    M.objIsoTensor X.1 X.2

/-- `064M:` The additional coherence required for the pointwise fixed-right comparisons to form
a two-variable natural isomorphism.

This is deliberately an explicit proposition rather than a typeclass.  The fields of
`DerivedTensor.Right.Monoidal.Model` only specify a left-derived model separately for each right
factor, so two-variable naturality cannot be recovered from that family alone. -/
@[stacks 064M "derived tensor to ambient tensor naturality"]
abbrev IsNatural
    (B : DerivedTensor.Bifunctor.Model (C := C))
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C,
      DerivedTensor.Bifunctor.Right.Model.Compatible B E) : Prop :=
  ∀ {X Y : DerivedCategory C × DerivedCategory C} (f : X ⟶ Y),
    B.functor.map f ≫ (objIsoTensorOfModels B M h Y).hom =
      (objIsoTensorOfModels B M h X).hom ≫
        (MonoidalCategory.tensor (DerivedCategory C)).map f

/-- `064M:` The functor-level comparison from an explicit two-variable model to ambient tensor. -/
@[stacks 064M "derived tensor to ambient tensor functor comparison"]
noncomputable def functorIsoTensorOfModels
    (B : DerivedTensor.Bifunctor.Model (C := C))
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C,
      DerivedTensor.Bifunctor.Right.Model.Compatible B E)
    (hn : IsNatural B M h) :
    B.functor ≅ MonoidalCategory.tensor (DerivedCategory C) :=
  NatIso.ofComponents (objIsoTensorOfModels B M h)
    hn

/-- The forward component of the explicit-model bifunctor comparison. -/
@[simp, stacks 064M "derived tensor to ambient tensor forward component"]
theorem functorIsoTensorOfModels_hom_app
    (B : DerivedTensor.Bifunctor.Model (C := C))
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C,
      DerivedTensor.Bifunctor.Right.Model.Compatible B E)
    (hn : IsNatural B M h)
    (X : DerivedCategory C × DerivedCategory C) :
    (functorIsoTensorOfModels B M h hn).hom.app X =
      (objIsoTensorOfModels B M h X).hom := rfl

/-- The inverse component of the explicit-model bifunctor comparison. -/
@[simp, stacks 064M "derived tensor to ambient tensor inverse component"]
theorem functorIsoTensorOfModels_inv_app
    (B : DerivedTensor.Bifunctor.Model (C := C))
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C,
      DerivedTensor.Bifunctor.Right.Model.Compatible B E)
    (hn : IsNatural B M h)
    (X : DerivedCategory C × DerivedCategory C) :
    (functorIsoTensorOfModels B M h hn).inv.app X =
      (objIsoTensorOfModels B M h X).inv := rfl

/-- The explicit bifunctor comparison agrees pointwise with the fixed-right model comparison. -/
@[reassoc (attr := simp), stacks 064M "bifunctor and fixed-right tensor comparison agreement"]
theorem isoAppOf_comp_objIsoTensorOfModels_hom
    (B : DerivedTensor.Bifunctor.Model (C := C))
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C,
      DerivedTensor.Bifunctor.Right.Model.Compatible B E)
    (X : DerivedCategory C × DerivedCategory C) :
    (DerivedTensor.Bifunctor.Right.Model.isoAppOf B X.2 (h X.2) X.1).hom ≫
        (objIsoTensorOfModels B M h X).hom =
      (M.objIsoTensor X.1 X.2).hom := by
  change
    (DerivedTensor.Bifunctor.Right.Model.isoAppOf B X.2 (h X.2) X.1).hom ≫
        ((DerivedTensor.Bifunctor.Right.Model.isoAppOf B X.2 (h X.2) X.1).symm ≪≫
          M.objIsoTensor X.1 X.2).hom =
      (M.objIsoTensor X.1 X.2).hom
  rw [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

/-- Inverse pointwise agreement with the fixed-right model comparison. -/
@[reassoc (attr := simp), stacks 064M "inverse bifunctor and fixed-right tensor agreement"]
theorem objIsoTensorOfModels_inv_comp_isoAppOf
    (B : DerivedTensor.Bifunctor.Model (C := C))
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C,
      DerivedTensor.Bifunctor.Right.Model.Compatible B E)
    (X : DerivedCategory C × DerivedCategory C) :
    (objIsoTensorOfModels B M h X).inv ≫
        (DerivedTensor.Bifunctor.Right.Model.isoAppOf B X.2 (h X.2) X.1).inv =
      (M.objIsoTensor X.1 X.2).inv := by
  change
    ((DerivedTensor.Bifunctor.Right.Model.isoAppOf B X.2 (h X.2) X.1).symm ≪≫
        M.objIsoTensor X.1 X.2).inv ≫
        (DerivedTensor.Bifunctor.Right.Model.isoAppOf B X.2 (h X.2) X.1).inv =
      (M.objIsoTensor X.1 X.2).inv
  rw [Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- Precomposition form of inverse pointwise agreement with the fixed-right model. -/
@[reassoc (attr := simp),
  stacks 064M "precomposition inverse bifunctor and fixed-right tensor agreement"]
theorem comp_objIsoTensorOfModels_inv_comp_isoAppOf
    (B : DerivedTensor.Bifunctor.Model (C := C))
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C,
      DerivedTensor.Bifunctor.Right.Model.Compatible B E)
    (X : DerivedCategory C × DerivedCategory C)
    {Z : DerivedCategory C}
    (f : Z ⟶ (MonoidalCategory.tensor (DerivedCategory C)).obj X) :
    f ≫ (objIsoTensorOfModels B M h X).inv ≫
        (DerivedTensor.Bifunctor.Right.Model.isoAppOf B X.2 (h X.2) X.1).inv =
      f ≫ (M.objIsoTensor X.1 X.2).inv := by
  exact congrArg (fun g ↦ f ≫ g)
    (objIsoTensorOfModels_inv_comp_isoAppOf B M h X)

section Canonical

variable [DerivedTensor.Bifunctor.Has (C := C)]

/-- `064M:` The objectwise comparison for the canonical two-variable derived tensor model. -/
@[stacks 064M "canonical derived tensor to ambient tensor object comparison"]
noncomputable abbrev objIsoTensorOf
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C, DerivedTensor.Bifunctor.Right.Compatible E)
    (X : DerivedCategory C × DerivedCategory C) :
    DerivedTensor.Bifunctor.functor.obj X ≅
      (MonoidalCategory.tensor (DerivedCategory C)).obj X :=
  objIsoTensorOfModels (DerivedTensor.Bifunctor.Right.canonicalModel (C := C)) M h X

/-- `064M:` Two-variable naturality of the canonical objectwise comparison, kept as an explicit
gate because fixed-right compatibility is only pointwise in the right factor. -/
@[stacks 064M "canonical derived tensor to ambient tensor naturality"]
abbrev IsNaturalOf
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C, DerivedTensor.Bifunctor.Right.Compatible E) : Prop :=
  IsNatural (DerivedTensor.Bifunctor.Right.canonicalModel (C := C)) M h

/-- `064M:` The functor-level comparison for the canonical two-variable derived tensor model. -/
@[stacks 064M "canonical derived tensor to ambient tensor functor comparison"]
noncomputable abbrev functorIsoTensorOf
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C, DerivedTensor.Bifunctor.Right.Compatible E)
    (hn : IsNaturalOf M h) :
    DerivedTensor.Bifunctor.functor (C := C) ≅
      MonoidalCategory.tensor (DerivedCategory C) :=
  functorIsoTensorOfModels
    (DerivedTensor.Bifunctor.Right.canonicalModel (C := C)) M h hn

end Canonical

end CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Monoidal
