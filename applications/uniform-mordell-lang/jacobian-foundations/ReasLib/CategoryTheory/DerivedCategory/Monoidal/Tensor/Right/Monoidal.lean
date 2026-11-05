module

public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Model
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Source
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fixed-right derived tensoring from a monoidal localization

This leaf compares the canonical fixed-right derived tensor functor with tensoring in a monoidal
structure on the derived category.  The general API consumes an explicit counit and its
left-derived universal property.  The `Strong` namespace constructs those inputs when the
homotopy localization itself is strong monoidal.  Neither path installs proof-local compatibility
instances.
@stack 064M
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.DerivedTensor.Right.Monoidal

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [∀ K L : CochainComplex C ℤ,
  HomologicalComplex.HasMapBifunctor K L (curriedTensor C) (up ℤ)]
variable [MonoidalCategory (DerivedCategory C)]

/-- Stacks 064M: a family of ambient fixed-right models, one for every derived right factor. -/
@[stacks 064M "ambient fixed-right model family"]
structure Model where
  /-- The ambient counit for each fixed right factor. -/
  counit (E : DerivedCategory C) :
    DerivedTensor.Right.localization (C := C) ⋙ MonoidalCategory.tensorRight E ⟶
      DerivedTensor.Right.sourceFunctor E
  /-- The ambient counit satisfies the fixed-right left-derived universal property. -/
  isLeftDerived (E : DerivedCategory C) :
    (MonoidalCategory.tensorRight E).IsLeftDerivedFunctor (counit E)
      (DerivedTensor.Right.qis (C := C))

/-- Stacks 064M: construct the ambient right-tensor model from an explicit counit and its
left-derived universal property. -/
@[stacks 064M "ambient fixed-right model constructor"]
noncomputable def modelOf (E : DerivedCategory C)
    (ε : DerivedTensor.Right.localization (C := C) ⋙ MonoidalCategory.tensorRight E ⟶
      DerivedTensor.Right.sourceFunctor E)
    (h : (MonoidalCategory.tensorRight E).IsLeftDerivedFunctor ε
      (DerivedTensor.Right.qis (C := C))) :
    DerivedTensor.Right.Model E :=
  DerivedTensor.Right.Model.of E (MonoidalCategory.tensorRight E) ε h

namespace Model

/-- Stacks 064M: extract the fixed-right model at a chosen derived object from an ambient model
family. -/
@[stacks 064M "ambient model family fixed-right specialization"]
noncomputable abbrev fixedRight (M : Model (C := C)) (E : DerivedCategory C) :
    DerivedTensor.Right.Model E :=
  modelOf E (M.counit E) (M.isLeftDerived E)

/-- Stacks 064M: compare canonical fixed-right derived tensoring with an ambient model family. -/
@[stacks 064M "ambient model family comparison"]
noncomputable abbrev functorIsoTensorRight (M : Model (C := C))
    (E : DerivedCategory C) [DerivedTensor.Right.Has (C := C)] :
    DerivedTensor.Right.functor E ≅ MonoidalCategory.tensorRight E :=
  DerivedTensor.Right.modelIso E (fixedRight M E)

/-- Stacks 064M: objectwise comparison supplied by an ambient model family. -/
@[stacks 064M "ambient model family object comparison"]
noncomputable abbrev objIsoTensor (M : Model (C := C))
    (K E : DerivedCategory C) [DerivedTensor.Right.Has (C := C)] :
    DerivedTensor.Right.obj K E ≅ K ⊗ E :=
  (functorIsoTensorRight M E).app K

/-- The forward map of the objectwise model comparison is the corresponding component of the
functor comparison. -/
@[simp, stacks 064M "ambient model family object comparison forward map"]
theorem objIsoTensor_hom (M : Model (C := C))
    (K E : DerivedCategory C) [DerivedTensor.Right.Has (C := C)] :
    (objIsoTensor M K E).hom = (M.functorIsoTensorRight E).hom.app K := rfl

/-- The inverse map of the objectwise model comparison is the corresponding inverse component of
the functor comparison. -/
@[simp, stacks 064M "ambient model family object comparison inverse map"]
theorem objIsoTensor_inv (M : Model (C := C))
    (K E : DerivedCategory C) [DerivedTensor.Right.Has (C := C)] :
    (objIsoTensor M K E).inv = (M.functorIsoTensorRight E).inv.app K := rfl

/-- The forward objectwise model comparison is natural in the left tensor factor. -/
@[reassoc, stacks 064M "ambient model family object comparison naturality"]
theorem objIsoTensor_naturality (M : Model (C := C))
    (E : DerivedCategory C) [DerivedTensor.Right.Has (C := C)]
    {K₁ K₂ : DerivedCategory C} (f : K₁ ⟶ K₂) :
    (DerivedTensor.Right.functor E).map f ≫ (objIsoTensor M K₂ E).hom =
      (objIsoTensor M K₁ E).hom ≫ (f ⊗ₘ 𝟙 E) := by
  rw [objIsoTensor_hom, objIsoTensor_hom, MonoidalCategory.tensorHom_id]
  exact (M.functorIsoTensorRight E).hom.naturality f

/-- The inverse objectwise model comparison is natural in the left tensor factor. -/
@[reassoc, stacks 064M "ambient model family inverse object comparison naturality"]
theorem objIsoTensor_inv_naturality (M : Model (C := C))
    (E : DerivedCategory C) [DerivedTensor.Right.Has (C := C)]
    {K₁ K₂ : DerivedCategory C} (f : K₁ ⟶ K₂) :
    (f ⊗ₘ 𝟙 E) ≫ (objIsoTensor M K₂ E).inv =
      (objIsoTensor M K₁ E).inv ≫ (DerivedTensor.Right.functor E).map f := by
  rw [objIsoTensor_inv, objIsoTensor_inv, MonoidalCategory.tensorHom_id]
  exact (M.functorIsoTensorRight E).inv.naturality f

/-- Stacks 064M: compare fixed-right derived tensoring by an object identified with the ambient
tensor unit with the identity functor.  The unit identification is explicit because a chosen
derived monoidal structure need not be canonically tied to a particular representative. -/
@[stacks 064M "fixed-right derived tensor unit comparison"]
noncomputable def functorIsoUnit (M : Model (C := C)) (E : DerivedCategory C)
    (s : E ≅ 𝟙_ (DerivedCategory C)) [DerivedTensor.Right.Has (C := C)] :
    DerivedTensor.Right.functor E ≅ 𝟭 (DerivedCategory C) :=
  M.functorIsoTensorRight E ≪≫
    ((curriedTensor (DerivedCategory C)).flip.mapIso s) ≪≫
    rightUnitorNatIso (DerivedCategory C)

section Braided

variable [BraidedCategory (DerivedCategory C)]

/-- Stacks 064M: compare ambient left tensoring with the canonical fixed-right derived tensor by
transporting through the derived-category braiding. -/
@[stacks 064M "ambient left tensor to fixed-right comparison"]
noncomputable abbrev tensorLeftIsoFunctor (M : Model (C := C))
    (E : DerivedCategory C) [DerivedTensor.Right.Has (C := C)] :
  MonoidalCategory.tensorLeft E ≅ DerivedTensor.Right.functor E :=
  BraidedCategory.tensorLeftIsoTensorRight E ≪≫
    (functorIsoTensorRight M E).symm

end Braided

/-- Stacks 064M: counit compatibility for the comparison supplied by an ambient model family. -/
@[reassoc (attr := simp), stacks 064M "ambient model family counit compatibility"]
theorem functorIsoTensorRight_counit (M : Model (C := C))
    (E : DerivedCategory C) [DerivedTensor.Right.Has (C := C)] :
    Functor.whiskerLeft (DerivedTensor.Right.localization (C := C))
        (functorIsoTensorRight M E).hom ≫ M.counit E =
      DerivedTensor.Right.counit E :=
  DerivedTensor.Right.modelIso_counit E (M.fixedRight E)

/-- Stacks 064M: objectwise counit compatibility for an ambient model family. -/
@[reassoc (attr := simp), stacks 064M "ambient model family object counit compatibility"]
theorem objIsoTensor_counit (M : Model (C := C))
    (E : DerivedCategory C) [DerivedTensor.Right.Has (C := C)]
    (K : HomotopyCategory C (up ℤ)) :
    (objIsoTensor M ((DerivedTensor.Right.localization (C := C)).obj K) E).hom ≫
        (M.counit E).app K = (DerivedTensor.Right.counit E).app K :=
  DerivedTensor.Right.modelIsoApp_counit E (M.fixedRight E) K

end Model

/-- Stacks 064M: compare canonical fixed-right derived tensoring with an ambient tensor model
presented by an explicit counit and universal-property law. -/
@[stacks 064M "fixed-right comparison with an ambient tensor model"]
noncomputable abbrev functorIsoTensorRightOf (E : DerivedCategory C)
    (ε : DerivedTensor.Right.localization (C := C) ⋙ MonoidalCategory.tensorRight E ⟶
      DerivedTensor.Right.sourceFunctor E)
    (h : (MonoidalCategory.tensorRight E).IsLeftDerivedFunctor ε
      (DerivedTensor.Right.qis (C := C)))
    [DerivedTensor.Right.Has (C := C)] :
    DerivedTensor.Right.functor E ≅ MonoidalCategory.tensorRight E :=
  DerivedTensor.Right.modelIso E (modelOf E ε h)

/-- Stacks 064M: the explicit ambient-model comparison intertwines its counit with the
canonical fixed-right counit. -/
@[reassoc (attr := simp), stacks 064M "ambient tensor model counit compatibility"]
theorem functorIsoTensorRightOf_counit (E : DerivedCategory C)
    (ε : DerivedTensor.Right.localization (C := C) ⋙ MonoidalCategory.tensorRight E ⟶
      DerivedTensor.Right.sourceFunctor E)
    (h : (MonoidalCategory.tensorRight E).IsLeftDerivedFunctor ε
      (DerivedTensor.Right.qis (C := C)))
    [DerivedTensor.Right.Has (C := C)] :
    Functor.whiskerLeft (DerivedTensor.Right.localization (C := C))
        (functorIsoTensorRightOf E ε h).hom ≫ ε =
      DerivedTensor.Right.counit E :=
  DerivedTensor.Right.modelIso_counit E (modelOf E ε h)

/-- Stacks 064M: objectwise counit compatibility for an explicitly presented ambient tensor
model. -/
@[reassoc (attr := simp), stacks 064M "ambient tensor model object counit compatibility"]
theorem objIsoTensorOf_counit (E : DerivedCategory C)
    (ε : DerivedTensor.Right.localization (C := C) ⋙ MonoidalCategory.tensorRight E ⟶
      DerivedTensor.Right.sourceFunctor E)
    (h : (MonoidalCategory.tensorRight E).IsLeftDerivedFunctor ε
      (DerivedTensor.Right.qis (C := C)))
    [DerivedTensor.Right.Has (C := C)] (K : HomotopyCategory C (up ℤ)) :
    (functorIsoTensorRightOf E ε h).hom.app
        ((DerivedTensor.Right.localization (C := C)).obj K) ≫
        ε.app K = (DerivedTensor.Right.counit E).app K :=
  DerivedTensor.Right.modelIsoApp_counit E (modelOf E ε h) K

namespace Strong

variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ C,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [HomotopyCategory.Koszul.TensorDescends (C := C)]
variable [(DerivedTensor.Right.localization (C := C)).Monoidal]

/-- Stacks 064M: under a strong monoidal localization, compare ambient right tensoring after
localization with the fixed-right homotopy source functor. -/
@[stacks 064M "monoidal fixed-right source comparison"]
noncomputable def sourceIso (E : DerivedCategory C) :
    DerivedTensor.Right.localization (C := C) ⋙ MonoidalCategory.tensorRight E ≅
      DerivedTensor.Right.sourceFunctor E :=
  Functor.isoWhiskerLeft (DerivedTensor.Right.localization (C := C))
      ((MonoidalCategory.tensoringRight (DerivedCategory C)).mapIso
        (DerivedTensor.Right.representativeIso E)).symm ≪≫
    Functor.Monoidal.commTensorRight
      (DerivedTensor.Right.localization (C := C))
      ((HomotopyCategory.quotient C (up ℤ)).obj
        ((DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C).objPreimage E)) ≪≫
    DerivedTensor.Right.sourceFunctorIso E

/-- Stacks 064M: ambient right tensoring, equipped with `sourceIso E`, satisfies the
fixed-right left-derived universal property. -/
@[stacks 064M "monoidal fixed-right derived compatibility"]
theorem sourceIso_isLeftDerived (E : DerivedCategory C) :
    (MonoidalCategory.tensorRight E).IsLeftDerivedFunctor
      (sourceIso E).hom (DerivedTensor.Right.qis (C := C)) :=
  Functor.isLeftDerivedFunctor_of_inverts
    (DerivedTensor.Right.qis (C := C)) (MonoidalCategory.tensorRight E) (sourceIso E)

/-- Stacks 064M: the explicit fixed-right derived model supplied by a compatible ambient
monoidal localization. -/
@[stacks 064M "monoidal fixed-right derived model"]
noncomputable def model (E : DerivedCategory C) : DerivedTensor.Right.Model E :=
  modelOf E (sourceIso E).hom (sourceIso_isLeftDerived E)

/-- Stacks 064M: the canonical strong-localization ambient model family. -/
@[stacks 064M "strong monoidal ambient model family"]
noncomputable def modelFamily : Model (C := C) where
  counit := fun E => (sourceIso E).hom
  isLeftDerived := sourceIso_isLeftDerived

/-- Stacks 064M: the canonical fixed-right derived tensor functor agrees with ambient right
tensoring. -/
@[stacks 064M "fixed-right derived tensor is ambient tensor"]
noncomputable abbrev functorIsoTensorRight (E : DerivedCategory C)
    [DerivedTensor.Right.Has (C := C)] :
    DerivedTensor.Right.functor E ≅ MonoidalCategory.tensorRight E :=
  functorIsoTensorRightOf E (sourceIso E).hom (sourceIso_isLeftDerived E)

/-- Stacks 064M: objectwise comparison from canonical fixed-right derived tensoring to ambient
right tensoring. -/
@[stacks 064M "fixed-right derived tensor object is ambient tensor"]
noncomputable abbrev objIsoTensor (K E : DerivedCategory C)
    [DerivedTensor.Right.Has (C := C)] :
    DerivedTensor.Right.obj K E ≅ K ⊗ E :=
  (functorIsoTensorRight E).app K

/-- Stacks 064M: the functor comparison intertwines the ambient-model and canonical
fixed-right counits. -/
@[reassoc (attr := simp), stacks 064M "monoidal fixed-right counit compatibility"]
theorem functorIsoTensorRight_counit (E : DerivedCategory C)
    [DerivedTensor.Right.Has (C := C)] :
    Functor.whiskerLeft (DerivedTensor.Right.localization (C := C))
        (functorIsoTensorRight E).hom ≫ (sourceIso E).hom =
      DerivedTensor.Right.counit E :=
  functorIsoTensorRightOf_counit E (sourceIso E).hom (sourceIso_isLeftDerived E)

/-- Stacks 064M: objectwise counit compatibility for the comparison with ambient right
tensoring. -/
@[reassoc (attr := simp), stacks 064M "monoidal fixed-right object counit compatibility"]
theorem objIsoTensor_counit (E : DerivedCategory C)
    [DerivedTensor.Right.Has (C := C)] (K : HomotopyCategory C (up ℤ)) :
    (objIsoTensor ((DerivedTensor.Right.localization (C := C)).obj K) E).hom ≫
        (sourceIso E).hom.app K = (DerivedTensor.Right.counit E).app K :=
  objIsoTensorOf_counit E (sourceIso E).hom (sourceIso_isLeftDerived E) K

end Strong

end CategoryTheory.DerivedCategory.DerivedTensor.Right.Monoidal
