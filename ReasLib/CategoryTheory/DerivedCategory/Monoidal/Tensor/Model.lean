/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Bifunctor
public import ReasLib.CategoryTheory.Functor.Derived.Model

/-!
# Explicit models for the derived tensor bifunctor

The existence predicate in `Tensor/Bifunctor.lean` supports mathlib's choice-based
`totalLeftDerived` construction.  This leaf instead bundles a selected derived tensor bifunctor
together with its counit. Consequently downstream constructions can depend on the selected data
explicitly, while the Kan-extension universal property remains proof data.
@stack 064M
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.DerivedTensor

namespace Bifunctor

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

/-- Stacks 064M: an explicit two-variable derived tensor model is the generic left-derived model
for the product localization of the homotopy tensor source.  The generic owner supplies the
concrete bifunctor, counit, and universal-property field; this namespace only adds tensor-specific
views and compatibility bridges. -/
@[stacks 064M "explicit two-variable derived tensor model"]
abbrev Model : Type _ :=
  Functor.LeftDerived.Model (sourceFunctor (C := C))
    (localization (C := C)) (qis (C := C))

namespace Model

/-- The selected bifunctor of a two-variable derived tensor model. -/
@[stacks 064M "explicit two-variable model functor"]
abbrev functor (M : Model (C := C)) :
    DerivedCategory C × DerivedCategory C ⥤ DerivedCategory C :=
  Functor.LeftDerived.Model.functor M

/-- The comparison counit of a two-variable derived tensor model. -/
@[stacks 064M "explicit two-variable model counit"]
abbrev counit (M : Model (C := C)) :
    localization (C := C) ⋙ M.functor ⟶ sourceFunctor (C := C) :=
  Functor.LeftDerived.Model.counit M

/-- The left-derived universal-property law carried by a two-variable tensor model. -/
@[stacks 064M "explicit two-variable model law"]
abbrev isLeftDerived (M : Model (C := C)) :
    M.functor.IsLeftDerivedFunctor M.counit (qis (C := C)) :=
  Functor.LeftDerived.Model.isLeftDerived M

/-- The fixed-left view of an explicit two-variable derived tensor model. -/
@[stacks 064M "explicit two-variable fixed-left view"]
noncomputable abbrev leftFunctor (M : Model (C := C)) (K : DerivedCategory C) :
    DerivedCategory C ⥤ DerivedCategory C :=
  (Functor.curry.obj M.functor).obj K

/-- The fixed-right view of an explicit two-variable derived tensor model. -/
@[stacks 064M "explicit two-variable fixed-right view"]
noncomputable abbrev rightFunctor (M : Model (C := C)) (L : DerivedCategory C) :
    DerivedCategory C ⥤ DerivedCategory C :=
  (Functor.curry.obj M.functor).flip.obj L

/-- The value of an explicit two-variable derived tensor model. -/
@[stacks 064M "explicit two-variable derived-tensor object"]
noncomputable abbrev obj (M : Model (C := C))
    (K L : DerivedCategory C) : DerivedCategory C :=
  M.functor.obj (K, L)

/-- The component of the counit of an explicit two-variable derived tensor model. -/
@[stacks 064M "explicit two-variable derived-tensor counit component"]
noncomputable abbrev counitApp (M : Model (C := C))
    (K L : HomotopyCategory C (up ℤ)) :
    M.obj
        ((DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C).obj K)
        ((DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C).obj L) ⟶
      (sourceFunctor (C := C)).obj (K, L) :=
  M.counit.app (K, L)

end Model

end Bifunctor

end CategoryTheory.DerivedCategory.DerivedTensor
