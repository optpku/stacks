module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Value
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Right

/-!
# Naturality of Bounded-Below Right-Derived Values

This leaf makes the bounded-below value construction functorial in the functor being derived.
It works for an arbitrary fixed localization model and is independent of cohomology or any
spectral-sequence construction.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived.Bounded

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

/-- A natural transformation between functors on the bounded-below homotopy category induces a
natural transformation between their value functors, computed with the same localization model.
-/
@[stacks 015H "naturality of bounded-below total right-derived values"]
noncomputable abbrev valueNatTrans
    {G H : HomotopyCategory.Plus A ⥤ D}
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [G.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [H.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    (τ : G ⟶ H) : valueFunctor G Q ⟶ valueFunctor H Q :=
  Functor.whiskerLeft (HomotopyCategory.Plus.quotient A ⋙ Q)
    (Functor.RightDerived.mapNatTrans Q (HomotopyCategory.Plus.quasiIso A) τ)

namespace valueNatTrans

/-- A component of `valueNatTrans` is the corresponding total right-derived component evaluated
at the localized bounded-below complex. -/
@[simp, stacks 015H "component of bounded-below total right-derived value naturality"]
theorem app
    {G H : HomotopyCategory.Plus A ⥤ D}
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [G.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [H.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    (τ : G ⟶ H) (K : CochainComplex.Plus A) :
    (valueNatTrans Q τ).app K =
      (Functor.RightDerived.mapNatTrans
        Q (HomotopyCategory.Plus.quasiIso A) τ).app
        (Q.obj ((HomotopyCategory.Plus.quotient A).obj K)) := sorry

/-- Naturality of a transformation between bounded-below right-derived value functors, expressed
using the source-facing `valueMap` API. -/
@[reassoc, stacks 015H "naturality square for bounded-below total right-derived values"]
theorem naturality
    {G H : HomotopyCategory.Plus A ⥤ D}
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [G.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [H.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    (τ : G ⟶ H) {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    valueMap G Q f ≫ (valueNatTrans Q τ).app L =
      (valueNatTrans Q τ).app K ≫ valueMap H Q f := sorry

/-- The bounded-below value construction preserves identity natural transformations. -/
@[simp, stacks 015H "identity of bounded-below total right-derived value naturality"]
theorem id
    (G : HomotopyCategory.Plus A ⥤ D)
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [G.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)] :
    valueNatTrans Q (𝟙 G) = 𝟙 (valueFunctor G Q) := sorry

/-- The bounded-below value construction preserves composition of natural transformations. -/
@[simp, stacks 015H "composition of bounded-below total right-derived value naturality"]
theorem comp
    {G H J : HomotopyCategory.Plus A ⥤ D}
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [G.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [H.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [J.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    (τ : G ⟶ H) (σ : H ⟶ J) :
    valueNatTrans Q (τ ≫ σ) = valueNatTrans Q τ ≫ valueNatTrans Q σ := sorry

/-- An invertible transformation induces an invertible transformation of bounded-below
right-derived value functors. -/
@[stacks 015H "isomorphism preservation for bounded-below total right-derived values"]
noncomputable instance isIso
    {G H : HomotopyCategory.Plus A ⥤ D}
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [G.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [H.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    (τ : G ⟶ H) [IsIso τ] : IsIso (valueNatTrans Q τ) := sorry

end valueNatTrans

end CategoryTheory.Functor.RightDerived.Bounded
