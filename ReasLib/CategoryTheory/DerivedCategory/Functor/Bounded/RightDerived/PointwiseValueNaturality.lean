/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.PointwiseValue
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Naturality.Functor.Right
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of bounded-below pointwise right-derived values

This leaf transports natural transformations through the canonical bounded-below homotopy
quotient. It does not choose a localization model, so it is the naturality counterpart of
`RightDerived.PointwiseValue` rather than of `RightDerived.Value`.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.RightDerived.Bounded

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {D : Type u₂} [Category.{v₂} D]

namespace PointwiseValue

/-- A natural transformation induces one between bounded-below pointwise value functors. -/
@[stacks 05SA "naturality of bounded-below pointwise right-derived values"]
noncomputable abbrev natTrans
    {G H : HomotopyCategory.Plus A ⥤ D} (τ : G ⟶ H)
    [G.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [H.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)] :
    pointwiseValueFunctor G ⟶ pointwiseValueFunctor H :=
  Functor.whiskerLeft (HomotopyCategory.Plus.quotient A)
    (Functor.RightDerived.Value.mapNatTrans
      (HomotopyCategory.Plus.quasiIso A) τ)

/-- The component of `PointwiseValue.natTrans` is the canonical pointwise component. -/
@[simp, stacks 05SA "component of bounded-below pointwise right-derived naturality"]
theorem natTrans_app
    {G H : HomotopyCategory.Plus A ⥤ D} (τ : G ⟶ H)
    [G.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [H.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    (K : CochainComplex.Plus A) :
    (natTrans τ).app K =
      Functor.RightDerived.Value.mapNatTrans.component
        (HomotopyCategory.Plus.quasiIso A) τ
        ((HomotopyCategory.Plus.quotient A).obj K) := sorry

/-- Naturality of the bounded-below pointwise component in the cochain complex. -/
@[reassoc, stacks 05SA "naturality square for bounded-below pointwise values"]
theorem natTrans_naturality
    {G H : HomotopyCategory.Plus A ⥤ D} (τ : G ⟶ H)
    [G.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [H.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    pointwiseValueMap G f ≫ (natTrans τ).app L =
      (natTrans τ).app K ≫ pointwiseValueMap H f := sorry

/-- Pointwise values preserve identity natural transformations. -/
@[simp, stacks 05SA "identity of bounded-below pointwise right-derived naturality"]
theorem natTrans_id
    (G : HomotopyCategory.Plus A ⥤ D)
    [G.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)] :
    natTrans (𝟙 G) = 𝟙 (pointwiseValueFunctor G) := sorry

/-- Pointwise values preserve vertical composition of natural transformations. -/
@[simp, stacks 05SA "composition of bounded-below pointwise right-derived naturality"]
theorem natTrans_comp
    {G H J : HomotopyCategory.Plus A ⥤ D}
    (τ : G ⟶ H) (σ : H ⟶ J)
    [G.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [H.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [J.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)] :
    natTrans (τ ≫ σ) = natTrans τ ≫ natTrans σ := sorry

namespace natTrans

alias app := natTrans_app
alias naturality := natTrans_naturality
alias id := natTrans_id
alias comp := natTrans_comp

end natTrans

end PointwiseValue

end CategoryTheory.Functor.RightDerived.Bounded
