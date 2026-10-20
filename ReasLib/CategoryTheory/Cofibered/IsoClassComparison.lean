/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import ReasLib.CategoryTheory.Cofibered.FiberIsoClass

/-!
# Isomorphism classes of categorical fibre products

A cleavage presents the two-fibre product of fibres of a category cofibered in
groupoids as a categorical pullback of pushforward functors. Projection induces
a comparison with the type-level fibre product of fibrewise isomorphism classes.
-/

@[expose] public section

open CategoryTheory Limits CategoricalPullback
open scoped CategoricalPullback

universe uC vC uF vF

variable {C : Type uC} [Category.{vC} C]
variable {F : Type uF} [Category.{vF} F]

namespace CategoryTheory.Functor

/-- The two projected isomorphism classes of an object of the fibre two-fibre
product agree after pushforward to the common base object. -/
theorem fiberProductIsoClassComparison_mem
    (p : F ⥤ C) [IsFibered.InGroupoids p.op]
    (χ : p.op.Cleavage) {A A1 A2 : C}
    (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (x : isomorphismClasses.obj
      (Cat.of ((pushforwardFiberFunctor p χ f1) ⊡ (pushforwardFiberFunctor p χ f2)))) :
    (fiberIsoClassFunctor p).map f1
        ((CategoricalPullback.π₁ (pushforwardFiberFunctor p χ f1)
            (pushforwardFiberFunctor p χ f2)).isoClassesMap x) =
      (fiberIsoClassFunctor p).map f2
        ((CategoricalPullback.π₂ (pushforwardFiberFunctor p χ f1)
            (pushforwardFiberFunctor p χ f2)).isoClassesMap x) :=
  sorry

/-- Projection from a categorical two-fibre product induces a map from its
isomorphism classes to the fibre product of fibrewise isomorphism classes. -/
noncomputable def fiberProductIsoClassComparison
    (p : F ⥤ C) [IsFibered.InGroupoids p.op]
    (χ : p.op.Cleavage) {A A1 A2 : C}
    (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) :
    isomorphismClasses.obj
      (Cat.of ((pushforwardFiberFunctor p χ f1) ⊡ (pushforwardFiberFunctor p χ f2))) →
      Types.PullbackObj ((fiberIsoClassFunctor p).map f1)
        ((fiberIsoClassFunctor p).map f2) :=
  fun x ↦
    ⟨⟨(CategoricalPullback.π₁ (pushforwardFiberFunctor p χ f1)
          (pushforwardFiberFunctor p χ f2)).isoClassesMap x,
      (CategoricalPullback.π₂ (pushforwardFiberFunctor p χ f1)
          (pushforwardFiberFunctor p χ f2)).isoClassesMap x⟩,
      fiberProductIsoClassComparison_mem p χ f1 f2 x⟩

/-- The coordinates of the comparison are the isomorphism classes induced by
the two projection functors. -/
theorem fiberProductIsoClassComparison_spec
    (p : F ⥤ C) [IsFibered.InGroupoids p.op]
    (χ : p.op.Cleavage) {A A1 A2 : C}
    (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (x : isomorphismClasses.obj
      (Cat.of ((pushforwardFiberFunctor p χ f1) ⊡ (pushforwardFiberFunctor p χ f2)))) :
    (fiberProductIsoClassComparison p χ f1 f2 x).1 =
      ((CategoricalPullback.π₁ (pushforwardFiberFunctor p χ f1)
          (pushforwardFiberFunctor p χ f2)).isoClassesMap x,
        (CategoricalPullback.π₂ (pushforwardFiberFunctor p χ f1)
          (pushforwardFiberFunctor p χ f2)).isoClassesMap x) :=
  sorry

/-- On a represented triple, the comparison is the pair of represented classes
of its two fibre objects. -/
theorem fiberProductIsoClassComparison_mk
    (p : F ⥤ C) [IsFibered.InGroupoids p.op]
    (χ : p.op.Cleavage) {A A1 A2 : C}
    (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) (x1 : p.Fiber A1) (x2 : p.Fiber A2)
    (e : (pushforwardFiberFunctor p χ f1).obj x1 ≅
      (pushforwardFiberFunctor p χ f2).obj x2) :
    (fiberProductIsoClassComparison p χ f1 f2 (Quotient.mk'' ⟨x1, x2, e⟩)).1 =
      (Quotient.mk'' x1, Quotient.mk'' x2) :=
  sorry

end CategoryTheory.Functor
