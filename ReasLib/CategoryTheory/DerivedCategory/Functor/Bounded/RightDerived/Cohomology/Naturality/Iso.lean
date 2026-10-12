/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Cohomology.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Value.Naturality.Iso

/-!
# Natural Isomorphisms of Bounded-Below Right-Derived Cohomology

This leaf transports natural isomorphisms of additive functors through a fixed bounded-below
localization model and then through target cohomology.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived.Bounded

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

/-- An isomorphism of additive functors induces an isomorphism of their bounded-below
right-derived cohomology functors, using the same localization model `Q`. -/
@[stacks 015H "natural isomorphism of bounded-below total right-derived cohomology"]
noncomputable abbrev cohomologyNatIso
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [G.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (e : F ≅ G) (n : ℤ) :
    cohomologyFunctor F Q n ≅ cohomologyFunctor G Q n :=
  Functor.isoWhiskerRight
    (valueNatIso Q (CategoryTheory.NatIso.toBoundedBelowDerived e))
    (DerivedCategory.Plus.homologyFunctor B n)

namespace cohomologyNatIso

/-- The forward map of `cohomologyNatIso` is induced by the forward transformation. -/
@[simp, stacks 015H "forward bounded-below right-derived cohomology isomorphism"]
theorem hom
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [G.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (e : F ≅ G) (n : ℤ) :
    (cohomologyNatIso Q e n).hom = cohomologyNatTrans Q e.hom n := sorry

/-- The inverse map of `cohomologyNatIso` is induced by the inverse transformation. -/
@[simp, stacks 015H "inverse bounded-below right-derived cohomology isomorphism"]
theorem inv
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [G.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (e : F ≅ G) (n : ℤ) :
    (cohomologyNatIso Q e n).inv = cohomologyNatTrans Q e.inv n := sorry

/-- The component of `cohomologyNatIso` is target cohomology applied to the corresponding
bounded-below right-derived value isomorphism. -/
@[simp, stacks 015H "component of bounded-below right-derived cohomology isomorphism"]
theorem app
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [G.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (e : F ≅ G) (n : ℤ) (K : CochainComplex.Plus A) :
    (cohomologyNatIso Q e n).app K =
      (DerivedCategory.Plus.homologyFunctor B n).mapIso
        ((valueNatIso Q (CategoryTheory.NatIso.toBoundedBelowDerived e)).app K) := sorry

/-- Right-derived cohomology preserves reflexive natural isomorphisms. -/
@[simp, stacks 015H "identity of bounded-below right-derived cohomology isomorphisms"]
theorem refl
    (F : A ⥤ B) [F.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (n : ℤ) :
    cohomologyNatIso Q (Iso.refl F) n = Iso.refl (cohomologyFunctor F Q n) := sorry

/-- Right-derived cohomology commutes with symmetry of natural isomorphisms. -/
@[simp, stacks 015H "symmetry of bounded-below right-derived cohomology isomorphisms"]
theorem symm
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [G.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (e : F ≅ G) (n : ℤ) :
    cohomologyNatIso Q e.symm n = (cohomologyNatIso Q e n).symm := sorry

/-- Right-derived cohomology commutes with transitivity of natural isomorphisms. -/
@[simp, stacks 015H "composition of bounded-below right-derived cohomology isomorphisms"]
theorem trans
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
    (e : F ≅ G) (e' : G ≅ H) (n : ℤ) :
    cohomologyNatIso Q (e ≪≫ e') n =
      cohomologyNatIso Q e n ≪≫ cohomologyNatIso Q e' n := sorry

end cohomologyNatIso

end CategoryTheory.Functor.RightDerived.Bounded
