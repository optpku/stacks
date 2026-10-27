/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Computation Rules for Right-Derived Natural Isomorphisms

These lemmas expose the universal-property equations for Mathlib's
`Functor.rightDerivedNatIso` on arbitrary right-derived presentations.
-/

@[expose] public section

noncomputable section

universe vC vD vH uC uD uH

namespace CategoryTheory.Functor.rightDerivedNatIso

variable {C : Type uC} {D : Type uD} {H : Type uH}
  [Category.{vC} C] [Category.{vD} D] [Category.{vH} H]
variable {F G : C ⥤ H} {L : C ⥤ D} (W : MorphismProperty C)
variable [L.IsLocalization W]

/-- The hom of an induced right-derived isomorphism satisfies the universal-property
factorization equation. -/
@[reassoc (attr := simp)]
theorem hom_fac
    (RF RG : D ⥤ H) (α : F ⟶ L ⋙ RF) (β : G ⟶ L ⋙ RG)
    [RF.IsRightDerivedFunctor α W] [RG.IsRightDerivedFunctor β W] (e : F ≅ G) :
    α ≫ whiskerLeft L (Functor.rightDerivedNatIso RF RG α β W e).hom =
      e.hom ≫ β := by
  change α ≫ whiskerLeft L (Functor.rightDerivedNatTrans RF RG α β W e.hom) =
    e.hom ≫ β
  exact Functor.rightDerivedNatTrans_fac RF RG α β W e.hom

/-- Objectwise universal-property equation for the hom of an induced right-derived
isomorphism. -/
@[reassoc (attr := simp)]
theorem hom_fac_app
    (RF RG : D ⥤ H) (α : F ⟶ L ⋙ RF) (β : G ⟶ L ⋙ RG)
    [RF.IsRightDerivedFunctor α W] [RG.IsRightDerivedFunctor β W]
    (e : F ≅ G) (X : C) :
    α.app X ≫ (Functor.rightDerivedNatIso RF RG α β W e).hom.app (L.obj X) =
      e.hom.app X ≫ β.app X := by
  change α.app X ≫
      (Functor.rightDerivedNatTrans RF RG α β W e.hom).app (L.obj X) =
    e.hom.app X ≫ β.app X
  exact Functor.rightDerivedNatTrans_app RF RG α β W e.hom X

/-- The inverse of an induced right-derived isomorphism satisfies the reverse
universal-property factorization equation. -/
@[reassoc (attr := simp)]
theorem inv_fac
    (RF RG : D ⥤ H) (α : F ⟶ L ⋙ RF) (β : G ⟶ L ⋙ RG)
    [RF.IsRightDerivedFunctor α W] [RG.IsRightDerivedFunctor β W] (e : F ≅ G) :
    β ≫ whiskerLeft L (Functor.rightDerivedNatIso RF RG α β W e).inv =
      e.inv ≫ α := by
  change β ≫ whiskerLeft L (Functor.rightDerivedNatTrans RG RF β α W e.inv) =
    e.inv ≫ α
  exact Functor.rightDerivedNatTrans_fac RG RF β α W e.inv

/-- Objectwise universal-property equation for the inverse of an induced right-derived
isomorphism. -/
@[reassoc (attr := simp)]
theorem inv_fac_app
    (RF RG : D ⥤ H) (α : F ⟶ L ⋙ RF) (β : G ⟶ L ⋙ RG)
    [RF.IsRightDerivedFunctor α W] [RG.IsRightDerivedFunctor β W]
    (e : F ≅ G) (X : C) :
    β.app X ≫ (Functor.rightDerivedNatIso RF RG α β W e).inv.app (L.obj X) =
      e.inv.app X ≫ α.app X := by
  change β.app X ≫
      (Functor.rightDerivedNatTrans RG RF β α W e.inv).app (L.obj X) =
    e.inv.app X ≫ α.app X
  exact Functor.rightDerivedNatTrans_app RG RF β α W e.inv X

end CategoryTheory.Functor.rightDerivedNatIso
