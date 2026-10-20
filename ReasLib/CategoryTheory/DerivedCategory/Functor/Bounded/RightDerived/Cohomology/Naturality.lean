/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Cohomology
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Value.Naturality

/-!
# Naturality of Bounded-Below Right-Derived Cohomology

This leaf transports natural transformations of additive functors through a chosen bounded-below
right-derived model and then through target cohomology.  The core cohomology object and map owners
remain in `RightDerived.Cohomology`; this file contains only the naturality layer.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived.Bounded

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

/-- A natural transformation of additive functors induces a natural transformation between their
bounded-below right-derived cohomology functors, using the same localization model `Q`. -/
@[stacks 015H "naturality of bounded-below total right-derived cohomology"]
noncomputable abbrev cohomologyNatTrans
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [G.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (τ : F ⟶ G) (n : ℤ) :
    cohomologyFunctor F Q n ⟶ cohomologyFunctor G Q n :=
  Functor.whiskerRight
    (valueNatTrans Q (CategoryTheory.NatTrans.toBoundedBelowDerived τ))
    (DerivedCategory.Plus.homologyFunctor B n)

/-- The component of `cohomologyNatTrans` is homology applied to the corresponding total
right-derived naturality map. -/
@[simp, stacks 015H "component of bounded-below total right-derived cohomology naturality"]
theorem cohomologyNatTrans_app
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [G.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (τ : F ⟶ G) (n : ℤ) (K : CochainComplex.Plus A) :
    (cohomologyNatTrans Q τ n).app K =
      (DerivedCategory.Plus.homologyFunctor B n).map
        ((valueNatTrans Q
          (CategoryTheory.NatTrans.toBoundedBelowDerived τ)).app K) := sorry

/-- Naturality of the cohomology comparison induced by a transformation of additive functors. -/
@[reassoc, stacks 015H "naturality square for bounded-below total right-derived cohomology"]
theorem cohomologyNatTrans_naturality
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [G.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (τ : F ⟶ G) (n : ℤ) {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    cohomologyMap F Q f n ≫ (cohomologyNatTrans Q τ n).app L =
      (cohomologyNatTrans Q τ n).app K ≫ cohomologyMap G Q f n := sorry

/-- Cohomology naturality preserves identity transformations of additive functors. -/
@[simp, stacks 015H "identity of bounded-below total right-derived cohomology naturality"]
theorem cohomologyNatTrans_id
    (F : A ⥤ B) [F.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (n : ℤ) :
    cohomologyNatTrans Q (𝟙 F) n = 𝟙 (cohomologyFunctor F Q n) := sorry

/-- Cohomology naturality preserves composition of transformations of additive functors. -/
@[simp, stacks 015H "composition of bounded-below total right-derived cohomology naturality"]
theorem cohomologyNatTrans_comp
    {F G H : A ⥤ B} [F.Additive] [G.Additive] [H.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [G.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [H.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (τ : F ⟶ G) (σ : G ⟶ H) (n : ℤ) :
    cohomologyNatTrans Q (τ ≫ σ) n =
      cohomologyNatTrans Q τ n ≫ cohomologyNatTrans Q σ n := sorry

namespace cohomologyNatTrans

/-- Canonical namespace spelling for the component computation. -/
alias app := cohomologyNatTrans_app

/-- Canonical namespace spelling for the naturality square. -/
alias naturality := cohomologyNatTrans_naturality

/-- Canonical namespace spelling for preservation of identities. -/
alias id := cohomologyNatTrans_id

/-- Canonical namespace spelling for preservation of composition. -/
alias comp := cohomologyNatTrans_comp

/-- An invertible transformation of additive functors induces an invertible transformation of
their bounded-below right-derived cohomology functors. -/
@[stacks 015H "isomorphism preservation for bounded-below right-derived cohomology"]
noncomputable instance isIso
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [G.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (τ : F ⟶ G) [IsIso τ] (n : ℤ) : IsIso (cohomologyNatTrans Q τ n) := sorry

end cohomologyNatTrans

end CategoryTheory.Functor.RightDerived.Bounded
