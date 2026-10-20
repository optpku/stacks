/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.SpectralSequence.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Cohomology.Naturality

/-!
# Naturality of Right-Derived Spectral-Sequence Abutments

This leaf exposes the naturality of the right-derived cohomology owner through the
application-facing abutment API.  It introduces no new realization data.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived.SpectralSequence

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

/-- A natural transformation of additive functors induces a natural transformation of their
degreewise right-derived spectral-sequence abutments. -/
@[stacks 015X "naturality of derived-functor spectral-sequence abutments"]
noncomputable abbrev abutmentNatTrans
    {T U : A ⥤ B} [T.Additive] [U.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [U.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (τ : T ⟶ U) (n : ℤ) :
    abutmentFunctor T Q n ⟶ abutmentFunctor U Q n :=
  Functor.RightDerived.Bounded.cohomologyNatTrans Q τ n

namespace abutmentNatTrans

/-- A component of the abutment transformation is target cohomology applied to the generic
bounded-below right-derived value transformation. -/
@[simp, stacks 015X "component of derived-functor spectral-sequence abutment naturality"]
theorem app
    {T U : A ⥤ B} [T.Additive] [U.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [U.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (τ : T ⟶ U) (n : ℤ) (K : CochainComplex.Plus A) :
    (abutmentNatTrans Q τ n).app K =
      (DerivedCategory.Plus.homologyFunctor B n).map
        ((Functor.RightDerived.Bounded.valueNatTrans Q
          (CategoryTheory.NatTrans.toBoundedBelowDerived τ)).app K) := sorry

/-- Naturality of the right-derived abutment transformation, expressed using `abutmentMap`. -/
@[reassoc, stacks 015X "naturality square for derived-functor spectral-sequence abutments"]
theorem naturality
    {T U : A ⥤ B} [T.Additive] [U.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [U.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (τ : T ⟶ U) (n : ℤ) {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    abutmentMap T Q f n ≫ (abutmentNatTrans Q τ n).app L =
      (abutmentNatTrans Q τ n).app K ≫ abutmentMap U Q f n := sorry

/-- Abutment naturality preserves the identity transformation. -/
@[simp, stacks 015X "identity of derived-functor spectral-sequence abutment naturality"]
theorem id
    (T : A ⥤ B) [T.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (n : ℤ) :
    abutmentNatTrans Q (𝟙 T) n = 𝟙 (abutmentFunctor T Q n) := sorry

/-- Abutment naturality preserves composition of transformations. -/
@[simp, stacks 015X "composition of derived-functor spectral-sequence abutment naturality"]
theorem comp
    {T U V : A ⥤ B} [T.Additive] [U.Additive] [V.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [U.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [V.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (τ : T ⟶ U) (σ : U ⟶ V) (n : ℤ) :
    abutmentNatTrans Q (τ ≫ σ) n =
      abutmentNatTrans Q τ n ≫ abutmentNatTrans Q σ n := sorry

/-- An invertible transformation induces an invertible transformation of right-derived
spectral-sequence abutment functors. -/
@[stacks 015X "isomorphism preservation for derived-functor spectral-sequence abutments"]
noncomputable instance isIso
    {T U : A ⥤ B} [T.Additive] [U.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [U.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (τ : T ⟶ U) [IsIso τ] (n : ℤ) : IsIso (abutmentNatTrans Q τ n) := sorry

end abutmentNatTrans

end CategoryTheory.Functor.RightDerived.SpectralSequence
