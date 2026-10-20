/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Model
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Braiding
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Model
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Source
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fixed-right views of the derived tensor bifunctor

The two-variable derived tensor has a canonical fixed-right view, but its source functor is
curried before localization.  This leaf records the comparison with the chosen-representative
source owner and packages the resulting functor as an explicit fixed-right model.  The concrete
functor and counit are public data; only the left-derived universal-property law remains a proof
field.
@stack 064M
@stack 0BYI
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor

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

namespace Right

/-- The homotopy quotient used for a fixed-right complex representative. -/
@[stacks 064M "fixed-right homotopy quotient"]
abbrev q : CochainComplex C ℤ ⥤ HomotopyCategory C (up ℤ) :=
  HomotopyCategory.quotient C (up ℤ)

/- The source is the fixed-right view of the curried two-variable source. -/
/-- Stacks 064M: the fixed-right source functor on a complex representative. -/
@[stacks 064M "fixed-right bifunctor source"]
noncomputable abbrev source (P : CochainComplex C ℤ) :
    HomotopyCategory C (up ℤ) ⥤ DerivedCategory C :=
  (Bifunctor.curriedSourceFunctor (C := C)).flip.obj (q.obj P)

/-- Stacks 064M: the fixed-right curry comparison for the homotopy tensor source. -/
@[stacks 064M "fixed-right source curry comparison"]
noncomputable def curryIso (P : CochainComplex C ℤ) :
    (Functor.curry.obj (Bifunctor.sourceFunctor (C := C))).flip.obj (q.obj P) ≅ source P :=
  eqToIso (congrArg (fun F => F.flip.obj (q.obj P))
    (Functor.curry_obj_uncurry_obj (Bifunctor.curriedSourceFunctor (C := C))))

/-- Stacks 064M: the canonical derived isomorphism from a chosen complex representative. -/
@[stacks 064M "fixed-right representative isomorphism"]
noncomputable abbrev repIso (E : DerivedCategory C) :
    DerivedCategory.Qh.obj (q.obj (DerivedCategory.Q.objPreimage E)) ≅ E :=
  DerivedTensor.Right.representativeIso E

/- The explicit-model namespace is the reusable core.  The declarations below do not require the
  choice-based `Bifunctor.Has` witness; they consume a concrete `Bifunctor.Model` instead. -/
namespace Model

/-- Stacks 064M: curry the localized functor of an explicit two-variable model. -/
@[stacks 064M "explicit fixed-right model source comparison"]
noncomputable def sourceIso (M : Bifunctor.Model (C := C)) (P : CochainComplex C ℤ) :
    (Functor.curry.obj (Bifunctor.localization (C := C) ⋙ M.functor)).flip.obj (q.obj P) ≅
      DerivedCategory.Qh ⋙ M.rightFunctor (DerivedCategory.Qh.obj (q.obj P)) :=
  ((flipFunctor _ _ _).mapIso
    (Functor.curryObjProdComp DerivedCategory.Qh DerivedCategory.Qh M.functor)).app (q.obj P)

/-- Stacks 064M: the fixed-right counit of an explicit two-variable model. -/
@[stacks 064M "explicit fixed-right model counit"]
noncomputable def counit (M : Bifunctor.Model (C := C)) (P : CochainComplex C ℤ) :
    DerivedCategory.Qh ⋙ M.rightFunctor (DerivedCategory.Qh.obj (q.obj P)) ⟶ source P :=
  (sourceIso M P).inv ≫
    (Functor.curry.map M.counit).flipApp (q.obj P) ≫
      (curryIso P).hom

/-- Stacks 064M: functoriality in the fixed right argument of an explicit model. -/
@[stacks 064M "explicit fixed-right representative isomorphism"]
noncomputable def rightRepIso (M : Bifunctor.Model (C := C)) (E : DerivedCategory C) :
    M.rightFunctor (DerivedCategory.Qh.obj (q.obj (DerivedCategory.Q.objPreimage E))) ≅
      M.rightFunctor E :=
  (Functor.curry.obj M.functor).flip.mapIso (repIso E)

/-- Stacks 064M: transport an explicit fixed-right counit to an arbitrary derived object. -/
@[stacks 064M "explicit fixed-right derived counit"]
noncomputable def counitOf (M : Bifunctor.Model (C := C)) (E : DerivedCategory C) :
    DerivedTensor.Right.localization (C := C) ⋙ M.rightFunctor E ⟶
      DerivedTensor.Right.sourceFunctor E :=
  Functor.whiskerLeft DerivedCategory.Qh (rightRepIso M E).inv ≫
    counit M (DerivedCategory.Q.objPreimage E) ≫
      (DerivedTensor.Right.sourceFunctorIso E).hom

/-- Stacks 064M: the extra law needed to regard a two-variable model as fixed-right derived. -/
@[stacks 064M "explicit fixed-right derived compatibility"]
abbrev Compatible (M : Bifunctor.Model (C := C)) (E : DerivedCategory C) : Prop :=
  (M.rightFunctor E).IsLeftDerivedFunctor
    (counitOf M E) (DerivedTensor.Right.qis (C := C))

/-- Stacks 064M: construct a fixed-right model from its compatibility proof. -/
@[stacks 064M "explicit fixed-right model constructor"]
noncomputable def of (M : Bifunctor.Model (C := C)) (E : DerivedCategory C)
    (hE : (M.rightFunctor E).IsLeftDerivedFunctor
      (counitOf M E) (DerivedTensor.Right.qis (C := C))) :
    DerivedTensor.Right.Model E :=
  DerivedTensor.Right.Model.of E (M.rightFunctor E) (counitOf M E) hE

/-- Stacks 064M: compare fixed-right derived tensor with an explicit two-variable model from a
supplied universal-property proof, without installing a local compatibility instance. -/
@[stacks 064M "explicit fixed-right comparison from a law"]
noncomputable abbrev isoOf (M : Bifunctor.Model (C := C)) (E : DerivedCategory C)
    (hE : (M.rightFunctor E).IsLeftDerivedFunctor
      (counitOf M E) (DerivedTensor.Right.qis (C := C)))
    [DerivedTensor.Right.Has (C := C)] :
    DerivedTensor.Right.functor E ≅ M.rightFunctor E :=
  DerivedTensor.Right.modelIso E (of M E hE)

/-- Stacks 064M: objectwise fixed-right comparison obtained from an explicit
universal-property proof. -/
@[stacks 064M "explicit fixed-right object comparison from a law"]
noncomputable abbrev isoAppOf (M : Bifunctor.Model (C := C)) (E : DerivedCategory C)
    (hE : (M.rightFunctor E).IsLeftDerivedFunctor
      (counitOf M E) (DerivedTensor.Right.qis (C := C)))
    [DerivedTensor.Right.Has (C := C)] (K : DerivedCategory C) :
    (DerivedTensor.Right.functor E).obj K ≅ (M.rightFunctor E).obj K :=
  (isoOf M E hE).app K

/-- Stacks 064M: the explicit-law fixed-right comparison intertwines the two counits. -/
@[reassoc (attr := simp), stacks 064M "explicit-law fixed-right counit compatibility"]
theorem isoOf_counit (M : Bifunctor.Model (C := C)) (E : DerivedCategory C)
    (hE : (M.rightFunctor E).IsLeftDerivedFunctor
      (counitOf M E) (DerivedTensor.Right.qis (C := C)))
    [DerivedTensor.Right.Has (C := C)] :
    Functor.whiskerLeft (DerivedTensor.Right.localization (C := C)) (isoOf M E hE).hom ≫
        counitOf M E = DerivedTensor.Right.counit E :=
  DerivedTensor.Right.modelIso_counit E (of M E hE)

/-- Stacks 064M: objectwise counit compatibility for the comparison built from an explicit law. -/
@[reassoc (attr := simp), stacks 064M "explicit-law fixed-right object counit compatibility"]
theorem isoAppOf_counit (M : Bifunctor.Model (C := C)) (E : DerivedCategory C)
    (hE : (M.rightFunctor E).IsLeftDerivedFunctor
      (counitOf M E) (DerivedTensor.Right.qis (C := C)))
    [DerivedTensor.Right.Has (C := C)] (K : HomotopyCategory C (up ℤ)) :
    (isoAppOf M E hE ((DerivedTensor.Right.localization (C := C)).obj K)).hom ≫
        (counitOf M E).app K = (DerivedTensor.Right.counit E).app K :=
  DerivedTensor.Right.modelIsoApp_counit E (of M E hE) K

/-- Stacks 064M: the fixed-right model selected by a compatibility instance. -/
@[stacks 064M "explicit compatible fixed-right model"]
noncomputable abbrev model (M : Bifunctor.Model (C := C)) (E : DerivedCategory C)
    [Compatible M E] : DerivedTensor.Right.Model E :=
  of M E inferInstance

/-- Stacks 064M: compare the canonical fixed-right derived functor with an explicit model. -/
@[stacks 064M "explicit fixed-right model comparison"]
noncomputable abbrev iso (M : Bifunctor.Model (C := C)) (E : DerivedCategory C)
    [Compatible M E] [DerivedTensor.Right.Has (C := C)] :
    DerivedTensor.Right.functor E ≅ M.rightFunctor E :=
  isoOf M E inferInstance

/-- Stacks 064M: objectwise comparison with an explicit fixed-right model. -/
@[stacks 064M "explicit fixed-right object comparison"]
noncomputable abbrev isoApp (M : Bifunctor.Model (C := C)) (E : DerivedCategory C)
    [Compatible M E] [DerivedTensor.Right.Has (C := C)] (K : DerivedCategory C) :
    (DerivedTensor.Right.functor E).obj K ≅ (M.rightFunctor E).obj K :=
  (iso M E).app K

/-- Stacks 064M: counit compatibility of the explicit fixed-right comparison. -/
@[reassoc (attr := simp), stacks 064M "explicit fixed-right counit compatibility"]
theorem iso_counit (M : Bifunctor.Model (C := C)) (E : DerivedCategory C)
    [Compatible M E] [DerivedTensor.Right.Has (C := C)] :
    Functor.whiskerLeft (DerivedTensor.Right.localization (C := C)) (iso M E).hom ≫
        counitOf M E = DerivedTensor.Right.counit E :=
  isoOf_counit M E inferInstance

/-- Stacks 064M: objectwise counit compatibility of the explicit comparison. -/
@[reassoc (attr := simp), stacks 064M "explicit fixed-right object counit compatibility"]
theorem isoApp_counit (M : Bifunctor.Model (C := C)) (E : DerivedCategory C)
    [Compatible M E] [DerivedTensor.Right.Has (C := C)]
    (K : HomotopyCategory C (up ℤ)) :
    (isoApp M E ((DerivedTensor.Right.localization (C := C)).obj K)).hom ≫
        (counitOf M E).app K = (DerivedTensor.Right.counit E).app K :=
  isoAppOf_counit M E inferInstance K

end Model

/-- Stacks 064M: the canonical explicit model selected by `Bifunctor.Has`. -/
@[stacks 064M "canonical two-variable derived tensor model"]
noncomputable abbrev canonicalModel [Bifunctor.Has (C := C)] :
    Bifunctor.Model (C := C) where
  functor := Bifunctor.functor
  counit := Bifunctor.counit
  isLeftDerived := inferInstance

/-- Stacks 064M: the product-localization curry comparison for the canonical bifunctor. -/
@[stacks 064M "fixed-right localization curry comparison"]
noncomputable abbrev sourceIso (P : CochainComplex C ℤ) [Bifunctor.Has (C := C)] :
    (Functor.curry.obj (Bifunctor.localization (C := C) ⋙ Bifunctor.functor (C := C))).flip.obj
        (q.obj P) ≅
      DerivedCategory.Qh ⋙ Bifunctor.rightFunctor (DerivedCategory.Qh.obj (q.obj P)) :=
  Model.sourceIso (canonicalModel (C := C)) P

/-- Stacks 064M: the two-variable derived counit viewed at a fixed right representative. -/
@[stacks 064M "fixed-right bifunctor counit"]
noncomputable abbrev counit (P : CochainComplex C ℤ) [Bifunctor.Has (C := C)] :
    DerivedCategory.Qh ⋙ Bifunctor.rightFunctor (DerivedCategory.Qh.obj (q.obj P)) ⟶ source P :=
  Model.counit (canonicalModel (C := C)) P

/-- Stacks 064M: functoriality of the bifunctor in the fixed right argument. -/
@[stacks 064M "fixed-right representative functor isomorphism"]
noncomputable abbrev rightRepIso (E : DerivedCategory C) [Bifunctor.Has (C := C)] :
    Bifunctor.rightFunctor
        (DerivedCategory.Qh.obj (q.obj (DerivedCategory.Q.objPreimage E))) ≅
      Bifunctor.rightFunctor E :=
  Model.rightRepIso (canonicalModel (C := C)) E

/-- Stacks 064M: the fixed-right bifunctor counit for a derived object. -/
@[stacks 064M "derived fixed-right bifunctor counit"]
noncomputable abbrev counitOf (E : DerivedCategory C)
    [Bifunctor.Has (C := C)] :
    DerivedTensor.Right.localization (C := C) ⋙ Bifunctor.rightFunctor E ⟶
      DerivedTensor.Right.sourceFunctor E :=
  Model.counitOf (canonicalModel (C := C)) E

/-- Stacks 064M: compatibility of the two-variable model with fixed-right derivation. -/
@[stacks 064M "fixed-right derived compatibility"]
abbrev Compatible (E : DerivedCategory C) [Bifunctor.Has (C := C)] : Prop :=
  Model.Compatible (canonicalModel (C := C)) E

/-- Stacks 064M: construct a fixed-right model from an explicit compatibility proof. -/
@[stacks 064M "fixed-right compatible model constructor"]
noncomputable def modelOf (E : DerivedCategory C)
    [Bifunctor.Has (C := C)]
    (hE : (Bifunctor.rightFunctor E).IsLeftDerivedFunctor
      (counitOf E) (DerivedTensor.Right.qis (C := C))) :
    DerivedTensor.Right.Model E :=
  Model.of (canonicalModel (C := C)) E hE

/-- Stacks 064M: compare canonical fixed-right tensoring with the bifunctor model from an explicit
compatibility proof, without introducing a local instance. -/
@[stacks 064M "fixed-right bifunctor comparison from a law"]
noncomputable abbrev isoOf (E : DerivedCategory C)
    [Bifunctor.Has (C := C)]
    (hE : (Bifunctor.rightFunctor E).IsLeftDerivedFunctor
      (counitOf E) (DerivedTensor.Right.qis (C := C)))
    [DerivedTensor.Right.Has (C := C)] :
    DerivedTensor.Right.functor E ≅ Bifunctor.rightFunctor E :=
  Model.isoOf (canonicalModel (C := C)) E hE

/-- Stacks 064M: objectwise bifunctor comparison obtained from an explicit compatibility proof. -/
@[stacks 064M "fixed-right bifunctor object comparison from a law"]
noncomputable abbrev isoAppOf (E : DerivedCategory C)
    [Bifunctor.Has (C := C)]
    (hE : (Bifunctor.rightFunctor E).IsLeftDerivedFunctor
      (counitOf E) (DerivedTensor.Right.qis (C := C)))
    [DerivedTensor.Right.Has (C := C)] (K : DerivedCategory C) :
    (DerivedTensor.Right.functor E).obj K ≅ (Bifunctor.rightFunctor E).obj K :=
  (isoOf E hE).app K

/-- Stacks 064M: the explicit-law bifunctor comparison intertwines the fixed-right counits. -/
@[reassoc (attr := simp), stacks 064M "fixed-right bifunctor explicit-law counit compatibility"]
theorem isoOf_counit (E : DerivedCategory C)
    [Bifunctor.Has (C := C)]
    (hE : (Bifunctor.rightFunctor E).IsLeftDerivedFunctor
      (counitOf E) (DerivedTensor.Right.qis (C := C)))
    [DerivedTensor.Right.Has (C := C)] :
    Functor.whiskerLeft (DerivedTensor.Right.localization (C := C)) (isoOf E hE).hom ≫
        counitOf E = DerivedTensor.Right.counit E :=
  Model.isoOf_counit (canonicalModel (C := C)) E hE

/-- Stacks 064M: objectwise counit compatibility for the explicit-law bifunctor comparison. -/
@[reassoc (attr := simp), stacks 064M
  "fixed-right bifunctor explicit-law object counit compatibility"]
theorem isoAppOf_counit (E : DerivedCategory C)
    [Bifunctor.Has (C := C)]
    (hE : (Bifunctor.rightFunctor E).IsLeftDerivedFunctor
      (counitOf E) (DerivedTensor.Right.qis (C := C)))
    [DerivedTensor.Right.Has (C := C)] (K : HomotopyCategory C (up ℤ)) :
    (isoAppOf E hE ((DerivedTensor.Right.localization (C := C)).obj K)).hom ≫
        (counitOf E).app K = (DerivedTensor.Right.counit E).app K :=
  Model.isoAppOf_counit (canonicalModel (C := C)) E hE K

/-- Stacks 064M: the fixed-right model supplied by a compatibility instance. -/
@[stacks 064M "derived fixed-right bifunctor model"]
noncomputable abbrev model (E : DerivedCategory C)
    [Bifunctor.Has (C := C)] [Compatible E] :
    DerivedTensor.Right.Model E :=
  Model.model (canonicalModel (C := C)) E

/-- Stacks 064M: comparison of the canonical fixed-right model with the bifunctor model. -/
@[stacks 064M "derived fixed-right bifunctor comparison"]
noncomputable abbrev iso (E : DerivedCategory C)
    [Bifunctor.Has (C := C)] [Compatible E] [DerivedTensor.Right.Has (C := C)] :
    DerivedTensor.Right.functor E ≅ Bifunctor.rightFunctor E :=
  isoOf E inferInstance

/-- Stacks 064M: the objectwise comparison of fixed-right derived tensor models. -/
@[stacks 064M "derived fixed-right bifunctor object comparison"]
noncomputable abbrev isoApp (E : DerivedCategory C)
    [Bifunctor.Has (C := C)] [Compatible E] [DerivedTensor.Right.Has (C := C)]
    (K : DerivedCategory C) :
    (DerivedTensor.Right.functor E).obj K ≅ (Bifunctor.rightFunctor E).obj K :=
  Model.isoApp (canonicalModel (C := C)) E K

section Symmetric

variable [SymmetricCategory C]

/-- Stacks 0BYI: symmetry of fixed-right derived tensoring, transported through the canonical
two-variable derived model.  This avoids identifying the ambient tensor on the derived category
with fixed-right derivation unless an explicit monoidal model supplies that comparison. -/
@[stacks 0BYI "fixed-right derived tensor symmetry"]
noncomputable def comm (K L : DerivedCategory C)
    [Bifunctor.Has (C := C)] [Compatible K] [Compatible L]
    [DerivedTensor.Right.Has (C := C)] :
    DerivedTensor.Right.obj K L ≅ DerivedTensor.Right.obj L K :=
  isoApp L K ≪≫ Bifunctor.comm K L ≪≫ (isoApp K L).symm

end Symmetric

/-- Stacks 064M: the fixed-right model comparison intertwines the counits. -/
@[reassoc (attr := simp), stacks 064M "derived fixed-right bifunctor counit compatibility"]
theorem iso_counit (E : DerivedCategory C)
    [Bifunctor.Has (C := C)] [Compatible E] [DerivedTensor.Right.Has (C := C)] :
    Functor.whiskerLeft (DerivedTensor.Right.localization (C := C)) (iso E).hom ≫
        counitOf E = DerivedTensor.Right.counit E :=
  isoOf_counit E inferInstance

/-- Stacks 064M: objectwise counit compatibility for the fixed-right comparison. -/
@[reassoc (attr := simp), stacks 064M "derived fixed-right bifunctor object counit compatibility"]
theorem isoApp_counit (E : DerivedCategory C)
    [Bifunctor.Has (C := C)] [Compatible E] [DerivedTensor.Right.Has (C := C)]
    (K : HomotopyCategory C (up ℤ)) :
    (isoApp E ((DerivedTensor.Right.localization (C := C)).obj K)).hom ≫
        (counitOf E).app K = (DerivedTensor.Right.counit E).app K :=
  isoAppOf_counit E inferInstance K

end Right

end CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor
