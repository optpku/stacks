/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import ReasLib.Algebra.Homology.HomotopyCategory.Monoidal
public import ReasLib.CategoryTheory.MorphismProperty.Product
import Mathlib.Tactic.CrossRefAttribute

/-!
# Two-variable derived tensor products

The tensor product on the homotopy category is a genuine bifunctor.  Its total left derived
functor is therefore taken with respect to the product of the two quasi-isomorphism classes.
This supplies functoriality in both variables and the canonical counit to ordinary totalized
tensor, independently of any chosen monoidal model on the derived category.
@stack 064M
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The product property is the canonical denominator owner for the two-variable construction. -/
@[stacks 064M "two-variable derived-tensor denominators"]
abbrev qis : MorphismProperty
    (HomotopyCategory C (up ℤ) × HomotopyCategory C (up ℤ)) :=
  (HomotopyCategory.quasiIso C (up ℤ)).prod
    (HomotopyCategory.quasiIso C (up ℤ))

/-- Membership in the product denominator property is componentwise quasi-isomorphism. -/
@[simp, stacks 064M "componentwise two-variable derived-tensor denominator"]
theorem qis_iff {X Y : HomotopyCategory C (up ℤ) × HomotopyCategory C (up ℤ)}
    (f : X ⟶ Y) :
    qis f ↔
      HomotopyCategory.quasiIso C (up ℤ) f.1 ∧
        HomotopyCategory.quasiIso C (up ℤ) f.2 := sorry

variable [HasDerivedCategory.{w} C]

/-- The product localization is kept separate from the derived bifunctor so model comparisons can
  mention its source and target without unfolding the choice-based construction. -/
@[stacks 064M "two-variable derived-tensor localization"]
abbrev localization :
    HomotopyCategory C (up ℤ) × HomotopyCategory C (up ℤ) ⥤
      DerivedCategory C × DerivedCategory C :=
  (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C).prod
    (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C)

variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ C,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [HomotopyCategory.Koszul.TensorDescends (C := C)]

/-- The curried source owner is the totalized homotopy tensor followed pointwise by localization. -/
@[stacks 064M "curried two-variable derived-tensor source"]
abbrev curriedSourceFunctor :
    HomotopyCategory C (up ℤ) ⥤
      HomotopyCategory C (up ℤ) ⥤ DerivedCategory C :=
  (Functor.postcompose₂.obj
    (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C)).obj
      (curriedTensor (HomotopyCategory C (up ℤ)))

/-- The uncurried source owner used by `totalLeftDerived`. -/
@[stacks 064M "two-variable derived-tensor source"]
abbrev sourceFunctor :
    HomotopyCategory C (up ℤ) × HomotopyCategory C (up ℤ) ⥤ DerivedCategory C :=
  Functor.uncurry.obj (curriedSourceFunctor (C := C))

/- The two presentations of the localized tensor source have definitionally equal objects.  The
  map-level compatibility is kept as a named proposition so downstream derived comparisons do not
  rebuild this transport at every specialization. -/
/-- `064M:` The tensor source written as tensoring in the homotopy category and then applying `Qh`. -/
@[stacks 064M "localized tensor source presentation"]
abbrev tensorSource :
    HomotopyCategory C (up ℤ) × HomotopyCategory C (up ℤ) ⥤ DerivedCategory C :=
  MonoidalCategory.tensor (HomotopyCategory C (up ℤ)) ⋙
    (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C)

/-- `064M:` The objectwise identity comparison between the two localized tensor source presentations. -/
@[stacks 064M "localized tensor source object comparison"]
noncomputable def sourceFunctorIsoApp
    (X : HomotopyCategory C (up ℤ) × HomotopyCategory C (up ℤ)) :
    tensorSource.obj X ≅ (sourceFunctor (C := C)).obj X :=
  eqToIso (by rfl)

/-- `064M:` Naturality of the identity comparison between the two localized tensor source presentations. -/
@[stacks 064M "localized tensor source comparison naturality"]
theorem sourceFunctorIso_naturality
    {X Y : HomotopyCategory C (up ℤ) × HomotopyCategory C (up ℤ)}
    (f : X ⟶ Y) :
    tensorSource.map f ≫ (sourceFunctorIsoApp Y).hom =
      (sourceFunctorIsoApp X).hom ≫ (sourceFunctor (C := C)).map f := sorry

/-- `064M:` The canonical natural isomorphism from the localized tensor source presentation to the
uncurried source owner used by the two-variable derived tensor. -/
@[stacks 064M "localized tensor source comparison"]
noncomputable def sourceFunctorIso :
    tensorSource ≅ sourceFunctor (C := C) :=
  NatIso.ofComponents sourceFunctorIsoApp sourceFunctorIso_naturality

/-- The existence gate is the canonical Mathlib left-derived-functor class for the product
localization.  The short name keeps tensor statements readable without introducing a parallel
one-field wrapper. -/
@[stacks 064M "two-variable derived-tensor existence"]
abbrev Has : Prop :=
  sourceFunctor (C := C) |>.HasLeftDerivedFunctor (qis (C := C))

/-- The total left derived tensor bifunctor. -/
@[stacks 064M "two-variable derived-tensor bifunctor"]
noncomputable abbrev functor [Has (C := C)] :
    DerivedCategory C × DerivedCategory C ⥤ DerivedCategory C :=
  (sourceFunctor (C := C)).totalLeftDerived
    (localization (C := C)) (qis (C := C))

/-- The fixed-left view of the two-variable derived tensor functor. -/
@[stacks 064M "two-variable fixed-left derived-tensor view"]
noncomputable abbrev leftFunctor (K : DerivedCategory C) [Has (C := C)] :
    DerivedCategory C ⥤ DerivedCategory C :=
  (Functor.curry.obj (functor (C := C))).obj K

/-- The fixed-right view of the two-variable derived tensor functor. -/
@[stacks 064M "two-variable fixed-right view"]
noncomputable abbrev rightFunctor (L : DerivedCategory C) [Has (C := C)] :
    DerivedCategory C ⥤ DerivedCategory C :=
  (Functor.curry.obj (functor (C := C))).flip.obj L

/-- The two-variable derived tensor product of two derived objects. -/
@[stacks 064M "two-variable derived-tensor object"]
noncomputable abbrev obj (K L : DerivedCategory C) [Has (C := C)] :
    DerivedCategory C :=
  (functor (C := C)).obj (K, L)

/-- The canonical counit from derived tensor to ordinary totalized tensor on homotopy objects. -/
@[stacks 064M "two-variable derived-tensor counit"]
noncomputable abbrev counit [Has (C := C)] :
    localization (C := C) ⋙ functor (C := C) ⟶ sourceFunctor (C := C) :=
  (sourceFunctor (C := C)).totalLeftDerivedCounit
    (localization (C := C)) (qis (C := C))

/-- The component of the canonical two-variable derived-tensor counit at a pair of homotopy
objects. -/
@[stacks 064M "two-variable derived tensor counit component"]
noncomputable abbrev counitApp (K L : HomotopyCategory C (up ℤ)) [Has (C := C)] :
    obj
        ((DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C).obj K)
        ((DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C).obj L) ⟶
      (sourceFunctor (C := C)).obj (K, L) :=
  (counit (C := C)).app (K, L)

/-- On cochain complexes, the source tensor bifunctor is the ordinary totalized tensor,
viewed in the derived category. -/
@[stacks 064M "ordinary tensor model of the two-variable source functor"]
noncomputable def sourceFunctorObjIso (K L : CochainComplex C ℤ) :
    (sourceFunctor (C := C)).obj
        ((HomotopyCategory.quotient C (up ℤ)).obj K,
          (HomotopyCategory.quotient C (up ℤ)).obj L) ≅
      (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C).obj (K ⊗ L) :=
  (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C).mapIso
      (Functor.Monoidal.μIso (HomotopyCategory.quotient C (up ℤ)) K L) ≪≫
    (DerivedCategory.quotientCompQhIso C).app (K ⊗ L)

/-- The two-variable derived-tensor counit on cochain complexes, with the ordinary tensor
complex as its explicit target. -/
@[stacks 064M "two-variable derived tensor counit on complexes"]
noncomputable def counitAppOfComplex (K L : CochainComplex C ℤ) [Has (C := C)] :
    obj
        ((DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C).obj
          ((HomotopyCategory.quotient C (up ℤ)).obj K))
        ((DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C).obj
          ((HomotopyCategory.quotient C (up ℤ)).obj L)) ⟶
      (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C).obj (K ⊗ L) :=
  counitApp
      ((HomotopyCategory.quotient C (up ℤ)).obj K)
      ((HomotopyCategory.quotient C (up ℤ)).obj L) ≫
    (sourceFunctorObjIso K L).hom

/-- The two-variable derived-tensor counit with the inputs presented directly by the derived
localization functor `DerivedCategory.Q`. -/
@[stacks 064M "two-variable derived tensor counit on localized complexes"]
noncomputable def counitAppOfQ (K L : CochainComplex C ℤ) [Has (C := C)] :
    obj (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ⟶
      DerivedCategory.Q.obj (K ⊗ L) :=
  (functor (C := C)).map
      (Prod.mkHom
        ((DerivedCategory.quotientCompQhIso C).inv.app K)
        ((DerivedCategory.quotientCompQhIso C).inv.app L)) ≫
    counitAppOfComplex K L

/-- The `Q`-presented counit is the homotopy-presented counit transported along the canonical
comparison `Qh (quotient K) ≅ Q K` in each input. -/
@[simp, reassoc (attr := simp), stacks 064M "localized complex counit factorization"]
theorem counitAppOfQ_fac (K L : CochainComplex C ℤ) [Has (C := C)] :
    counitAppOfQ K L =
      (functor (C := C)).map
          (Prod.mkHom
            ((DerivedCategory.quotientCompQhIso C).inv.app K)
            ((DerivedCategory.quotientCompQhIso C).inv.app L)) ≫
        counitAppOfComplex K L := sorry

/-- Transporting the inputs from `Q` to `Qh ∘ quotient` does not change whether the
complex-level derived-tensor counit is invertible. -/
@[simp, stacks 064M "localized complex counit invertibility transport"]
theorem counitAppOfQ_isIso_iff (K L : CochainComplex C ℤ) [Has (C := C)] :
    IsIso (counitAppOfQ K L) ↔ IsIso (counitAppOfComplex K L) := sorry

/-- The complex-level counit is the homotopy-level counit followed by the canonical
identification of its source-functor value with the ordinary tensor complex. -/
@[simp, reassoc (attr := simp), stacks 064M "complex-level counit factorization"]
theorem counitAppOfComplex_fac (K L : CochainComplex C ℤ) [Has (C := C)] :
    counitAppOfComplex K L =
      counitApp
          ((HomotopyCategory.quotient C (up ℤ)).obj K)
          ((HomotopyCategory.quotient C (up ℤ)).obj L) ≫
        (sourceFunctorObjIso K L).hom := sorry

/-- Invertibility of the complex-level counit is equivalent to invertibility of the
underlying homotopy-level counit component. -/
@[simp, stacks 064M "complex-level counit invertibility transport"]
theorem counitAppOfComplex_isIso_iff (K L : CochainComplex C ℤ) [Has (C := C)] :
    IsIso (counitAppOfComplex K L) ↔
      IsIso
        (counitApp
          ((HomotopyCategory.quotient C (up ℤ)).obj K)
          ((HomotopyCategory.quotient C (up ℤ)).obj L)) := sorry

/-- Transport the canonical derived-tensor counit to an isomorphic two-variable model. -/
noncomputable def counitOfIso [Has (C := C)]
    (T : DerivedCategory C × DerivedCategory C ⥤ DerivedCategory C)
    (e : functor (C := C) ≅ T) :
    localization (C := C) ⋙ T ⟶ sourceFunctor (C := C) :=
  Functor.whiskerLeft (localization (C := C)) e.inv ≫ counit (C := C)

/-- Any supplied two-variable left-derived model is canonically isomorphic to the total
left-derived tensor bifunctor. -/
noncomputable abbrev modelIso [Has (C := C)]
    (T : DerivedCategory C × DerivedCategory C ⥤ DerivedCategory C)
    (ε : localization (C := C) ⋙ T ⟶ sourceFunctor (C := C))
    [T.IsLeftDerivedFunctor ε (qis (C := C))] :
    functor (C := C) ≅ T :=
  T.leftDerivedUnique (functor (C := C))
    (counit (C := C)) ε (qis (C := C))

/-- The counit transported along the canonical model isomorphism is the supplied model
counit. -/
theorem counitOfIso_modelIso [Has (C := C)]
    (T : DerivedCategory C × DerivedCategory C ⥤ DerivedCategory C)
    (ε : localization (C := C) ⋙ T ⟶ sourceFunctor (C := C))
    [T.IsLeftDerivedFunctor ε (qis (C := C))] :
    counitOfIso T (modelIso T ε) = ε := sorry

end CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor
