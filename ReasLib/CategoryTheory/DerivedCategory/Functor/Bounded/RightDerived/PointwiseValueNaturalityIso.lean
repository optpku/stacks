/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.PointwiseValueNaturality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Natural isomorphisms of bounded-below pointwise right-derived values

This leaf promotes a natural isomorphism of homotopy-category functors to the corresponding
pointwise value functors, with component and inverse computation views.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.RightDerived.Bounded

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {D : Type u₂} [Category.{v₂} D]

namespace PointwiseValue

/-- A natural isomorphism induces one between bounded-below pointwise value functors. -/
@[stacks 05SA "natural isomorphism of bounded-below pointwise right-derived values"]
noncomputable abbrev natIso
    {G H : HomotopyCategory.Plus A ⥤ D} (e : G ≅ H)
    [G.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [H.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)] :
    pointwiseValueFunctor G ≅ pointwiseValueFunctor H :=
  Functor.isoWhiskerLeft (HomotopyCategory.Plus.quotient A)
    (Functor.RightDerived.Value.mapNatIso
      (HomotopyCategory.Plus.quasiIso A) e)

/-- The forward map of `PointwiseValue.natIso` is `PointwiseValue.natTrans` on `e.hom`. -/
@[simp, stacks 05SA "forward map of bounded-below pointwise right-derived natural isomorphism"]
theorem natIso_hom
    {G H : HomotopyCategory.Plus A ⥤ D} (e : G ≅ H)
    [G.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [H.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)] :
    (natIso e).hom = natTrans e.hom := sorry

/-- The inverse map of `PointwiseValue.natIso` is `PointwiseValue.natTrans` on `e.inv`. -/
@[simp, stacks 05SA "inverse map of bounded-below pointwise right-derived natural isomorphism"]
theorem natIso_inv
    {G H : HomotopyCategory.Plus A ⥤ D} (e : G ≅ H)
    [G.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [H.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)] :
    (natIso e).inv = natTrans e.inv := sorry

/-- The forward component of `PointwiseValue.natIso` is the pointwise comparison component. -/
@[simp, stacks 05SA "component of bounded-below pointwise right-derived natural isomorphism"]
theorem natIso_hom_app
    {G H : HomotopyCategory.Plus A ⥤ D} (e : G ≅ H)
    [G.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [H.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    (K : CochainComplex.Plus A) :
    (natIso e).hom.app K =
      (Functor.RightDerived.Value.mapNatIso.component
        (HomotopyCategory.Plus.quasiIso A) e
        ((HomotopyCategory.Plus.quotient A).obj K)).hom := sorry

/-- The inverse component of `PointwiseValue.natIso` is the pointwise inverse comparison. -/
@[simp, stacks 05SA "inverse component of bounded-below pointwise right-derived natural isomorphism"]
theorem natIso_inv_app
    {G H : HomotopyCategory.Plus A ⥤ D} (e : G ≅ H)
    [G.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [H.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    (K : CochainComplex.Plus A) :
    (natIso e).inv.app K =
      (Functor.RightDerived.Value.mapNatIso.component
        (HomotopyCategory.Plus.quasiIso A) e
        ((HomotopyCategory.Plus.quotient A).obj K)).inv := sorry

/-- Pointwise values preserve reflexivity of natural isomorphisms. -/
@[simp, stacks 05SA "identity of bounded-below pointwise right-derived natural isomorphisms"]
theorem natIso_refl
    (G : HomotopyCategory.Plus A ⥤ D)
    [G.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)] :
    natIso (Iso.refl G) = Iso.refl (pointwiseValueFunctor G) := sorry

/-- Pointwise values commute with symmetry of natural isomorphisms. -/
@[simp, stacks 05SA "symmetry of bounded-below pointwise right-derived natural isomorphisms"]
theorem natIso_symm
    {G H : HomotopyCategory.Plus A ⥤ D} (e : G ≅ H)
    [G.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [H.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)] :
    natIso e.symm = (natIso e).symm := sorry

/-- Pointwise values preserve transitivity of natural isomorphisms. -/
@[simp, stacks 05SA "composition of bounded-below pointwise right-derived natural isomorphisms"]
theorem natIso_trans
    {G H J : HomotopyCategory.Plus A ⥤ D} (e : G ≅ H) (e' : H ≅ J)
    [G.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [H.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    [J.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)] :
    natIso (e.trans e') = (natIso e).trans (natIso e') := sorry

namespace natIso

alias hom := natIso_hom
alias inv := natIso_inv
alias hom_app := natIso_hom_app
alias inv_app := natIso_inv_app
alias refl := natIso_refl
alias symm := natIso_symm
alias trans := natIso_trans

end natIso

end PointwiseValue

end CategoryTheory.Functor.RightDerived.Bounded
