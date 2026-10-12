/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Bifunctor.Monoidal
import Mathlib.Tactic.CrossRefAttribute
import Mathlib.Tactic.BDSimp

/-!
# Unit comparisons for the derived tensor bifunctor

@stack 064M

This leaf fixes the first variable of a two-variable derived tensor model at an object explicitly
identified with the ambient tensor unit.  It produces a functor-level comparison with the
identity and records its agreement with the corresponding fixed-right model.  No tensor-unit
object, monoidal structure, or model is inferred here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Monoidal.Unit

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [MonoidalCategory (DerivedCategory C)]

/-- Fix `U` as the first component of a pair while the second component varies. -/
@[stacks 064M "fixed-left pair functor"]
noncomputable def pair (U : DerivedCategory C) :
    DerivedCategory C ⥤ DerivedCategory C × DerivedCategory C where
  obj L := (U, L)
  map f := (𝟙 U, f)
  map_id L := by ext <;> simp
  map_comp f g := by ext <;> simp

/-- The ambient left-unit comparison at one target object. -/
@[stacks 064M "ambient fixed-left unit component"]
noncomputable abbrev ambientComponent
    (U : DerivedCategory C) (s : U ≅ 𝟙_ (DerivedCategory C))
    (L : DerivedCategory C) :
    (pair U ⋙ MonoidalCategory.tensor (DerivedCategory C)).obj L ≅ L :=
  whiskerRightIso s L ≪≫ λ_ L

/-- Naturality of the ambient left-unit comparison. -/
@[reassoc, stacks 064M "ambient fixed-left unit naturality"]
theorem ambientComponent_naturality
    (U : DerivedCategory C) (s : U ≅ 𝟙_ (DerivedCategory C))
    {L M : DerivedCategory C} (f : L ⟶ M) :
    (pair U ⋙ MonoidalCategory.tensor (DerivedCategory C)).map f ≫
      (ambientComponent U s M).hom =
      (ambientComponent U s L).hom ≫ f := by
  bdsimp only [pair]
  bdsimp only [ambientComponent]
  bdsimp only [MonoidalCategory.tensor]
  bdsimp only [Functor.comp]
  bdsimp only [pair]
  simp only [Iso.trans_hom, whiskerRightIso_hom, id_tensorHom]
  rw [Category.assoc, whisker_exchange_assoc, leftUnitor_naturality]

/-- The functor-level ambient comparison for a fixed object identified with the tensor unit. -/
@[stacks 064M "ambient fixed-left unit functor comparison"]
noncomputable def ambientIso
    (U : DerivedCategory C) (s : U ≅ 𝟙_ (DerivedCategory C)) :
    pair U ⋙ MonoidalCategory.tensor (DerivedCategory C) ≅
      𝟭 (DerivedCategory C) :=
  NatIso.ofComponents (ambientComponent U s)
    (ambientComponent_naturality U s)

/-- The forward component of the ambient unit comparison. -/
@[simp, stacks 064M "ambient fixed-left unit forward component"]
theorem ambientIso_hom_app
    (U : DerivedCategory C) (s : U ≅ 𝟙_ (DerivedCategory C))
    (L : DerivedCategory C) :
    (ambientIso U s).hom.app L = (ambientComponent U s L).hom := rfl

/-- The inverse component of the ambient unit comparison. -/
@[simp, stacks 064M "ambient fixed-left unit inverse component"]
theorem ambientIso_inv_app
    (U : DerivedCategory C) (s : U ≅ 𝟙_ (DerivedCategory C))
    (L : DerivedCategory C) :
    (ambientIso U s).inv.app L = (ambientComponent U s L).inv := rfl

/-- Inverse naturality of the ambient unit comparison. -/
@[reassoc, stacks 064M "inverse ambient fixed-left unit naturality"]
theorem ambientIso_inv_naturality
    (U : DerivedCategory C) (s : U ≅ 𝟙_ (DerivedCategory C))
    {L M : DerivedCategory C} (f : L ⟶ M) :
    f ≫ (ambientIso U s).inv.app M =
      (ambientIso U s).inv.app L ≫
        (pair U ⋙ MonoidalCategory.tensor (DerivedCategory C)).map f := by
  simpa using (ambientIso U s).inv.naturality f

variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ C,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [HomotopyCategory.Koszul.TensorDescends (C := C)]
variable [DerivedTensor.Right.Has (C := C)]

/-- The fixed-left unit comparison for an explicit two-variable derived tensor model. -/
@[stacks 064M "explicit derived bifunctor fixed-left unit comparison"]
noncomputable def functorIsoOfModels
    (B : DerivedTensor.Bifunctor.Model (C := C))
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C,
      DerivedTensor.Bifunctor.Right.Model.Compatible B E)
    (hn : DerivedTensor.Bifunctor.Monoidal.IsNatural B M h)
    (U : DerivedCategory C) (s : U ≅ 𝟙_ (DerivedCategory C)) :
    pair U ⋙ B.functor ≅ 𝟭 (DerivedCategory C) :=
  Functor.isoWhiskerLeft (pair U)
      (DerivedTensor.Bifunctor.Monoidal.functorIsoTensorOfModels B M h hn) ≪≫
    ambientIso U s

/-- The objectwise explicit-model fixed-left unit comparison. -/
@[stacks 064M "explicit derived bifunctor fixed-left unit object comparison"]
noncomputable abbrev objIsoOfModels
    (B : DerivedTensor.Bifunctor.Model (C := C))
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C,
      DerivedTensor.Bifunctor.Right.Model.Compatible B E)
    (hn : DerivedTensor.Bifunctor.Monoidal.IsNatural B M h)
    (U : DerivedCategory C) (s : U ≅ 𝟙_ (DerivedCategory C))
    (L : DerivedCategory C) :
    (pair U ⋙ B.functor).obj L ≅ L :=
  (functorIsoOfModels B M h hn U s).app L

/-- Naturality of the explicit-model fixed-left unit comparison. -/
@[reassoc, stacks 064M "explicit derived bifunctor fixed-left unit naturality"]
theorem functorIsoOfModels_naturality
    (B : DerivedTensor.Bifunctor.Model (C := C))
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C,
      DerivedTensor.Bifunctor.Right.Model.Compatible B E)
    (hn : DerivedTensor.Bifunctor.Monoidal.IsNatural B M h)
    (U : DerivedCategory C) (s : U ≅ 𝟙_ (DerivedCategory C))
    {L N : DerivedCategory C} (f : L ⟶ N) :
    (pair U ⋙ B.functor).map f ≫
        (functorIsoOfModels B M h hn U s).hom.app N =
      (functorIsoOfModels B M h hn U s).hom.app L ≫ f := by
  simpa using (functorIsoOfModels B M h hn U s).hom.naturality f

/-- Inverse naturality of the explicit-model fixed-left unit comparison. -/
@[reassoc, stacks 064M "inverse explicit derived bifunctor fixed-left unit naturality"]
theorem functorIsoOfModels_inv_naturality
    (B : DerivedTensor.Bifunctor.Model (C := C))
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C,
      DerivedTensor.Bifunctor.Right.Model.Compatible B E)
    (hn : DerivedTensor.Bifunctor.Monoidal.IsNatural B M h)
    (U : DerivedCategory C) (s : U ≅ 𝟙_ (DerivedCategory C))
    {L N : DerivedCategory C} (f : L ⟶ N) :
    f ≫ (functorIsoOfModels B M h hn U s).inv.app N =
      (functorIsoOfModels B M h hn U s).inv.app L ≫
        (pair U ⋙ B.functor).map f := by
  simpa using (functorIsoOfModels B M h hn U s).inv.naturality f

/-- Formula for the forward explicit-model component. -/
@[simp, stacks 064M "explicit derived bifunctor fixed-left unit forward component"]
theorem functorIsoOfModels_hom_app
    (B : DerivedTensor.Bifunctor.Model (C := C))
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C,
      DerivedTensor.Bifunctor.Right.Model.Compatible B E)
    (hn : DerivedTensor.Bifunctor.Monoidal.IsNatural B M h)
    (U : DerivedCategory C) (s : U ≅ 𝟙_ (DerivedCategory C))
    (L : DerivedCategory C) :
    (functorIsoOfModels B M h hn U s).hom.app L =
      (DerivedTensor.Bifunctor.Monoidal.functorIsoTensorOfModels B M h hn).hom.app
          ((pair U).obj L) ≫
        (ambientComponent U s L).hom := rfl

/-- Formula for the inverse explicit-model component. -/
@[simp, stacks 064M "explicit derived bifunctor fixed-left unit inverse component"]
theorem functorIsoOfModels_inv_app
    (B : DerivedTensor.Bifunctor.Model (C := C))
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C,
      DerivedTensor.Bifunctor.Right.Model.Compatible B E)
    (hn : DerivedTensor.Bifunctor.Monoidal.IsNatural B M h)
    (U : DerivedCategory C) (s : U ≅ 𝟙_ (DerivedCategory C))
    (L : DerivedCategory C) :
    (functorIsoOfModels B M h hn U s).inv.app L =
      (ambientComponent U s L).inv ≫
        (DerivedTensor.Bifunctor.Monoidal.functorIsoTensorOfModels B M h hn).inv.app
          ((pair U).obj L) := rfl

/-- The fixed-left object comparison obtained directly from the fixed-right model. -/
@[stacks 064M "fixed-right model left-unit object comparison"]
noncomputable def leftUnitObjIso
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (U : DerivedCategory C) (s : U ≅ 𝟙_ (DerivedCategory C))
    (L : DerivedCategory C) :
    DerivedTensor.Right.obj U L ≅ L :=
  M.objIsoTensor U L ≪≫ ambientComponent U s L

/-- The explicit bifunctor comparison agrees with the fixed-right comparison. -/
@[simp, stacks 064M "explicit bifunctor and fixed-right left-unit agreement"]
theorem functorIsoOfModels_agrees_hom
    (B : DerivedTensor.Bifunctor.Model (C := C))
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C,
      DerivedTensor.Bifunctor.Right.Model.Compatible B E)
    (hn : DerivedTensor.Bifunctor.Monoidal.IsNatural B M h)
    (U : DerivedCategory C) (s : U ≅ 𝟙_ (DerivedCategory C))
    (L : DerivedCategory C) :
    (DerivedTensor.Bifunctor.Right.Model.isoAppOf B L (h L) U).hom ≫
        (functorIsoOfModels B M h hn U s).hom.app L =
      (leftUnitObjIso M U s L).hom := by
  rw [functorIsoOfModels_hom_app,
    DerivedTensor.Bifunctor.Monoidal.functorIsoTensorOfModels_hom_app]
  bdsimp only [pair]
  change
    (DerivedTensor.Bifunctor.Right.Model.isoAppOf B L (h L) U).hom ≫
        (DerivedTensor.Bifunctor.Monoidal.objIsoTensorOfModels B M h (U, L)).hom ≫
          (ambientComponent U s L).hom =
      (M.objIsoTensor U L ≪≫ ambientComponent U s L).hom
  calc
    _ = ((DerivedTensor.Bifunctor.Right.Model.isoAppOf B L (h L) U).hom ≫
          (DerivedTensor.Bifunctor.Monoidal.objIsoTensorOfModels B M h (U, L)).hom) ≫
        (ambientComponent U s L).hom := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun g ↦ g ≫ (ambientComponent U s L).hom)
      (DerivedTensor.Bifunctor.Monoidal.isoAppOf_comp_objIsoTensorOfModels_hom
        B M h (U, L))

/-- The inverse explicit bifunctor comparison agrees with the inverse fixed-right comparison. -/
@[simp, stacks 064M "inverse explicit bifunctor and fixed-right left-unit agreement"]
theorem functorIsoOfModels_agrees_inv
    (B : DerivedTensor.Bifunctor.Model (C := C))
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C,
      DerivedTensor.Bifunctor.Right.Model.Compatible B E)
    (hn : DerivedTensor.Bifunctor.Monoidal.IsNatural B M h)
    (U : DerivedCategory C) (s : U ≅ 𝟙_ (DerivedCategory C))
    (L : DerivedCategory C) :
    (functorIsoOfModels B M h hn U s).inv.app L ≫
        (DerivedTensor.Bifunctor.Right.Model.isoAppOf B L (h L) U).inv =
      (leftUnitObjIso M U s L).inv := by
  rw [functorIsoOfModels_inv_app,
    DerivedTensor.Bifunctor.Monoidal.functorIsoTensorOfModels_inv_app]
  bdsimp only [pair]
  change
    ((ambientComponent U s L).inv ≫
        (DerivedTensor.Bifunctor.Monoidal.objIsoTensorOfModels B M h (U, L)).inv) ≫
      (DerivedTensor.Bifunctor.Right.Model.isoAppOf B L (h L) U).inv =
        (M.objIsoTensor U L ≪≫ ambientComponent U s L).inv
  calc
    _ = (ambientComponent U s L).inv ≫
        ((DerivedTensor.Bifunctor.Monoidal.objIsoTensorOfModels B M h (U, L)).inv ≫
          (DerivedTensor.Bifunctor.Right.Model.isoAppOf B L (h L) U).inv) :=
      Category.assoc _ _ _
    _ = _ := congrArg (fun g ↦ (ambientComponent U s L).inv ≫ g)
      (DerivedTensor.Bifunctor.Monoidal.objIsoTensorOfModels_inv_comp_isoAppOf
        B M h (U, L))

section Canonical

variable [DerivedTensor.Bifunctor.Has (C := C)]

/-- The fixed-left unit comparison for the canonical two-variable derived tensor model. -/
@[stacks 064M "canonical derived bifunctor fixed-left unit comparison"]
noncomputable abbrev functorIso
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C, DerivedTensor.Bifunctor.Right.Compatible E)
    (hn : DerivedTensor.Bifunctor.Monoidal.IsNaturalOf M h)
    (U : DerivedCategory C) (s : U ≅ 𝟙_ (DerivedCategory C)) :
    pair U ⋙ DerivedTensor.Bifunctor.functor (C := C) ≅
      𝟭 (DerivedCategory C) :=
  functorIsoOfModels
    (DerivedTensor.Bifunctor.Right.canonicalModel (C := C)) M h hn U s

/-- The objectwise canonical fixed-left unit comparison. -/
@[stacks 064M "canonical derived bifunctor fixed-left unit object comparison"]
noncomputable abbrev objIso
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C, DerivedTensor.Bifunctor.Right.Compatible E)
    (hn : DerivedTensor.Bifunctor.Monoidal.IsNaturalOf M h)
    (U : DerivedCategory C) (s : U ≅ 𝟙_ (DerivedCategory C))
    (L : DerivedCategory C) :
    (pair U ⋙ DerivedTensor.Bifunctor.functor (C := C)).obj L ≅ L :=
  (functorIso M h hn U s).app L

/-- Naturality of the canonical fixed-left unit comparison. -/
@[reassoc, stacks 064M "canonical derived bifunctor fixed-left unit naturality"]
theorem functorIso_naturality
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C, DerivedTensor.Bifunctor.Right.Compatible E)
    (hn : DerivedTensor.Bifunctor.Monoidal.IsNaturalOf M h)
    (U : DerivedCategory C) (s : U ≅ 𝟙_ (DerivedCategory C))
    {L N : DerivedCategory C} (f : L ⟶ N) :
    (pair U ⋙ DerivedTensor.Bifunctor.functor (C := C)).map f ≫
        (functorIso M h hn U s).hom.app N =
      (functorIso M h hn U s).hom.app L ≫ f :=
  functorIsoOfModels_naturality
    (DerivedTensor.Bifunctor.Right.canonicalModel (C := C)) M h hn U s f

/-- Inverse naturality of the canonical fixed-left unit comparison. -/
@[reassoc, stacks 064M "inverse canonical derived bifunctor fixed-left unit naturality"]
theorem functorIso_inv_naturality
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C, DerivedTensor.Bifunctor.Right.Compatible E)
    (hn : DerivedTensor.Bifunctor.Monoidal.IsNaturalOf M h)
    (U : DerivedCategory C) (s : U ≅ 𝟙_ (DerivedCategory C))
    {L N : DerivedCategory C} (f : L ⟶ N) :
    f ≫ (functorIso M h hn U s).inv.app N =
      (functorIso M h hn U s).inv.app L ≫
        (pair U ⋙ DerivedTensor.Bifunctor.functor (C := C)).map f :=
  functorIsoOfModels_inv_naturality
    (DerivedTensor.Bifunctor.Right.canonicalModel (C := C)) M h hn U s f

/-- Formula for the forward canonical component. -/
@[simp, stacks 064M "canonical derived bifunctor fixed-left unit forward component"]
theorem functorIso_hom_app
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C, DerivedTensor.Bifunctor.Right.Compatible E)
    (hn : DerivedTensor.Bifunctor.Monoidal.IsNaturalOf M h)
    (U : DerivedCategory C) (s : U ≅ 𝟙_ (DerivedCategory C))
    (L : DerivedCategory C) :
    (functorIso M h hn U s).hom.app L =
      (DerivedTensor.Bifunctor.Monoidal.functorIsoTensorOf M h hn).hom.app
          ((pair U).obj L) ≫
        (ambientComponent U s L).hom :=
  functorIsoOfModels_hom_app
    (DerivedTensor.Bifunctor.Right.canonicalModel (C := C)) M h hn U s L

/-- Formula for the inverse canonical component. -/
@[simp, stacks 064M "canonical derived bifunctor fixed-left unit inverse component"]
theorem functorIso_inv_app
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C, DerivedTensor.Bifunctor.Right.Compatible E)
    (hn : DerivedTensor.Bifunctor.Monoidal.IsNaturalOf M h)
    (U : DerivedCategory C) (s : U ≅ 𝟙_ (DerivedCategory C))
    (L : DerivedCategory C) :
    (functorIso M h hn U s).inv.app L =
      (ambientComponent U s L).inv ≫
        (DerivedTensor.Bifunctor.Monoidal.functorIsoTensorOf M h hn).inv.app
          ((pair U).obj L) :=
  functorIsoOfModels_inv_app
    (DerivedTensor.Bifunctor.Right.canonicalModel (C := C)) M h hn U s L

/-- The canonical bifunctor comparison agrees with the fixed-right comparison. -/
@[simp, stacks 064M "canonical bifunctor and fixed-right left-unit agreement"]
theorem functorIso_agrees_hom
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C, DerivedTensor.Bifunctor.Right.Compatible E)
    (hn : DerivedTensor.Bifunctor.Monoidal.IsNaturalOf M h)
    (U : DerivedCategory C) (s : U ≅ 𝟙_ (DerivedCategory C))
    (L : DerivedCategory C) :
    (DerivedTensor.Bifunctor.Right.isoAppOf L (h L) U).hom ≫
        (functorIso M h hn U s).hom.app L =
      (leftUnitObjIso M U s L).hom :=
  functorIsoOfModels_agrees_hom
    (DerivedTensor.Bifunctor.Right.canonicalModel (C := C)) M h hn U s L

/-- The inverse canonical bifunctor comparison agrees with the fixed-right comparison. -/
@[simp, stacks 064M "inverse canonical bifunctor and fixed-right left-unit agreement"]
theorem functorIso_agrees_inv
    (M : DerivedTensor.Right.Monoidal.Model (C := C))
    (h : ∀ E : DerivedCategory C, DerivedTensor.Bifunctor.Right.Compatible E)
    (hn : DerivedTensor.Bifunctor.Monoidal.IsNaturalOf M h)
    (U : DerivedCategory C) (s : U ≅ 𝟙_ (DerivedCategory C))
    (L : DerivedCategory C) :
    (functorIso M h hn U s).inv.app L ≫
        (DerivedTensor.Bifunctor.Right.isoAppOf L (h L) U).inv =
      (leftUnitObjIso M U s L).inv :=
  functorIsoOfModels_agrees_inv
    (DerivedTensor.Bifunctor.Right.canonicalModel (C := C)) M h hn U s L

end Canonical

end CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Monoidal.Unit
