/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Value.Naturality

/-!
# Natural Isomorphisms of Bounded-Below Right-Derived Values

An isomorphism between functors on the bounded-below homotopy category induces a natural
isomorphism between their value functors for a fixed localization model.  The construction is
kept separate from comparisons between different localization models.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived.Bounded

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

/-- An isomorphism on the bounded-below homotopy category induces an isomorphism of value
functors computed with a fixed localization model `Q`. -/
@[stacks 015H "natural isomorphism of bounded-below total right-derived values"]
noncomputable abbrev valueNatIso
    {G H : HomotopyCategory.Plus A ⥤ D}
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [G.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [H.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    (e : G ≅ H) : valueFunctor G Q ≅ valueFunctor H Q :=
  Functor.isoWhiskerLeft (HomotopyCategory.Plus.quotient A ⋙ Q)
    (Functor.RightDerived.mapNatIso Q (HomotopyCategory.Plus.quasiIso A) e)

namespace valueNatIso

/-- The forward component of `valueNatIso` is the transformation induced by `e.hom`. -/
@[simp, stacks 015H "forward component of bounded-below value natural isomorphism"]
theorem hom
    {G H : HomotopyCategory.Plus A ⥤ D}
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [G.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [H.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    (e : G ≅ H) : (valueNatIso Q e).hom = valueNatTrans Q e.hom := sorry

/-- The inverse component of `valueNatIso` is the transformation induced by `e.inv`. -/
@[simp, stacks 015H "inverse component of bounded-below value natural isomorphism"]
theorem inv
    {G H : HomotopyCategory.Plus A ⥤ D}
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [G.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [H.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    (e : G ≅ H) : (valueNatIso Q e).inv = valueNatTrans Q e.inv := sorry

/-- The component of `valueNatIso` at a bounded-below complex is the corresponding value
isomorphism after localizing that complex. -/
@[simp, stacks 015H "component of bounded-below value natural isomorphism"]
theorem app
    {G H : HomotopyCategory.Plus A ⥤ D}
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [G.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [H.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    (e : G ≅ H) (K : CochainComplex.Plus A) :
    (valueNatIso Q e).app K =
      (Functor.RightDerived.mapNatIso Q (HomotopyCategory.Plus.quasiIso A) e).app
        (Q.obj ((HomotopyCategory.Plus.quotient A).obj K)) := sorry

/-- The value construction preserves reflexive natural isomorphisms. -/
@[simp, stacks 015H "identity of bounded-below value natural isomorphisms"]
theorem refl
    (G : HomotopyCategory.Plus A ⥤ D)
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [G.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)] :
    valueNatIso Q (Iso.refl G) = Iso.refl (valueFunctor G Q) := sorry

/-- The value construction commutes with symmetry of natural isomorphisms. -/
@[simp, stacks 015H "symmetry of bounded-below value natural isomorphisms"]
theorem symm
    {G H : HomotopyCategory.Plus A ⥤ D}
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [G.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [H.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    (e : G ≅ H) : valueNatIso Q e.symm = (valueNatIso Q e).symm := sorry

/-- The value construction commutes with transitivity of natural isomorphisms. -/
@[simp, stacks 015H "composition of bounded-below value natural isomorphisms"]
theorem trans
    {G H J : HomotopyCategory.Plus A ⥤ D}
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [G.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [H.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [J.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    (e : G ≅ H) (e' : H ≅ J) :
    valueNatIso Q (e ≪≫ e') = valueNatIso Q e ≪≫ valueNatIso Q e' := sorry

end valueNatIso

end CategoryTheory.Functor.RightDerived.Bounded
