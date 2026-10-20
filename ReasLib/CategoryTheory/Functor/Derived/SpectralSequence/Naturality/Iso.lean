/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.SpectralSequence.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Cohomology.Naturality.Iso

/-!
# Natural Isomorphisms of Right-Derived Spectral-Sequence Abutments

This leaf presents bounded-below right-derived cohomology isomorphisms through the
application-facing abutment API.  It introduces no new realization or comparison data.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived.SpectralSequence

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]
variable {E : Type u₃} [Category.{v₃} E]
variable (Q : HomotopyCategory.Plus A ⥤ E)
  [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]

/-- An isomorphism of additive functors induces an isomorphism of their degreewise
right-derived spectral-sequence abutment functors. -/
@[stacks 015X "natural isomorphism of derived-functor spectral-sequence abutments"]
noncomputable abbrev abutmentNatIso
    {T U : A ⥤ B} [T.Additive] [U.Additive]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [U.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (e : T ≅ U) (n : ℤ) :
    abutmentFunctor T Q n ≅ abutmentFunctor U Q n :=
  Functor.RightDerived.Bounded.cohomologyNatIso Q e n

namespace abutmentNatIso

/-- The forward abutment isomorphism is induced by the forward transformation. -/
@[simp, stacks 015X "forward derived-functor abutment isomorphism"]
theorem hom
    {T U : A ⥤ B} [T.Additive] [U.Additive]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [U.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (e : T ≅ U) (n : ℤ) :
    (abutmentNatIso Q e n).hom = abutmentNatTrans Q e.hom n := sorry

/-- The inverse abutment isomorphism is induced by the inverse transformation. -/
@[simp, stacks 015X "inverse derived-functor abutment isomorphism"]
theorem inv
    {T U : A ⥤ B} [T.Additive] [U.Additive]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [U.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (e : T ≅ U) (n : ℤ) :
    (abutmentNatIso Q e n).inv = abutmentNatTrans Q e.inv n := sorry

/-- The component of the abutment isomorphism is the corresponding bounded-below
right-derived cohomology isomorphism. -/
@[simp, stacks 015X "component of derived-functor abutment isomorphism"]
theorem app
    {T U : A ⥤ B} [T.Additive] [U.Additive]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [U.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (e : T ≅ U) (n : ℤ) (K : CochainComplex.Plus A) :
    (abutmentNatIso Q e n).app K =
      (Functor.RightDerived.Bounded.cohomologyNatIso Q e n).app K := sorry

/-- Abutment naturality preserves reflexive natural isomorphisms. -/
@[simp, stacks 015X "identity of derived-functor abutment isomorphisms"]
theorem refl
    (T : A ⥤ B) [T.Additive]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (n : ℤ) :
    abutmentNatIso Q (Iso.refl T) n = Iso.refl (abutmentFunctor T Q n) := sorry

/-- Abutment naturality commutes with symmetry of natural isomorphisms. -/
@[simp, stacks 015X "symmetry of derived-functor abutment isomorphisms"]
theorem symm
    {T U : A ⥤ B} [T.Additive] [U.Additive]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [U.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (e : T ≅ U) (n : ℤ) :
    abutmentNatIso Q e.symm n = (abutmentNatIso Q e n).symm := sorry

/-- Abutment naturality commutes with transitivity of natural isomorphisms. -/
@[simp, stacks 015X "composition of derived-functor abutment isomorphisms"]
theorem trans
    {T U V : A ⥤ B} [T.Additive] [U.Additive] [V.Additive]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [U.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [V.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (e : T ≅ U) (e' : U ≅ V) (n : ℤ) :
    abutmentNatIso Q (e ≪≫ e') n =
      abutmentNatIso Q e n ≪≫ abutmentNatIso Q e' n := sorry

end abutmentNatIso

end CategoryTheory.Functor.RightDerived.SpectralSequence
