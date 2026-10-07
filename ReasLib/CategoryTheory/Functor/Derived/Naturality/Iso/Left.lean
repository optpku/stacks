module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Computation Rules for Left-Derived Natural Isomorphisms

These lemmas expose the universal-property equations for Mathlib's
`Functor.leftDerivedNatIso` on arbitrary left-derived presentations.
-/

@[expose] public section

noncomputable section

universe vC vD vH uC uD uH

namespace CategoryTheory.Functor.leftDerivedNatIso

variable {C : Type uC} {D : Type uD} {H : Type uH}
  [Category.{vC} C] [Category.{vD} D] [Category.{vH} H]
variable {F G : C ⥤ H} {L : C ⥤ D} (W : MorphismProperty C)
variable [L.IsLocalization W]

/-- The hom of an induced left-derived isomorphism satisfies the universal-property
factorization equation. -/
@[stacks 05T2, reassoc (attr := simp)]
theorem hom_fac
    (LF LG : D ⥤ H) (α : L ⋙ LF ⟶ F) (β : L ⋙ LG ⟶ G)
    [LF.IsLeftDerivedFunctor α W] [LG.IsLeftDerivedFunctor β W] (e : F ≅ G) :
    whiskerLeft L (Functor.leftDerivedNatIso LF LG α β W e).hom ≫ β =
      α ≫ e.hom := by
  change whiskerLeft L (Functor.leftDerivedNatTrans LF LG α β W e.hom) ≫ β =
    α ≫ e.hom
  exact Functor.leftDerivedNatTrans_fac LF LG α β W e.hom

/-- Objectwise universal-property equation for the hom of an induced left-derived
isomorphism. -/
@[stacks 05T2, reassoc (attr := simp)]
theorem hom_fac_app
    (LF LG : D ⥤ H) (α : L ⋙ LF ⟶ F) (β : L ⋙ LG ⟶ G)
    [LF.IsLeftDerivedFunctor α W] [LG.IsLeftDerivedFunctor β W]
    (e : F ≅ G) (X : C) :
    (Functor.leftDerivedNatIso LF LG α β W e).hom.app (L.obj X) ≫ β.app X =
      α.app X ≫ e.hom.app X := by
  change (Functor.leftDerivedNatTrans LF LG α β W e.hom).app (L.obj X) ≫
    β.app X = α.app X ≫ e.hom.app X
  exact Functor.leftDerivedNatTrans_app LF LG α β W e.hom X

/-- The inverse of an induced left-derived isomorphism satisfies the reverse
universal-property factorization equation. -/
@[stacks 05T2, reassoc (attr := simp)]
theorem inv_fac
    (LF LG : D ⥤ H) (α : L ⋙ LF ⟶ F) (β : L ⋙ LG ⟶ G)
    [LF.IsLeftDerivedFunctor α W] [LG.IsLeftDerivedFunctor β W] (e : F ≅ G) :
    whiskerLeft L (Functor.leftDerivedNatIso LF LG α β W e).inv ≫ α =
      β ≫ e.inv := by
  change whiskerLeft L (Functor.leftDerivedNatTrans LG LF β α W e.inv) ≫ α =
    β ≫ e.inv
  exact Functor.leftDerivedNatTrans_fac LG LF β α W e.inv

/-- Objectwise universal-property equation for the inverse of an induced left-derived
isomorphism. -/
@[stacks 05T2, reassoc (attr := simp)]
theorem inv_fac_app
    (LF LG : D ⥤ H) (α : L ⋙ LF ⟶ F) (β : L ⋙ LG ⟶ G)
    [LF.IsLeftDerivedFunctor α W] [LG.IsLeftDerivedFunctor β W]
    (e : F ≅ G) (X : C) :
    (Functor.leftDerivedNatIso LF LG α β W e).inv.app (L.obj X) ≫ α.app X =
      β.app X ≫ e.inv.app X := by
  change (Functor.leftDerivedNatTrans LG LF β α W e.inv).app (L.obj X) ≫
    α.app X = β.app X ≫ e.inv.app X
  exact Functor.leftDerivedNatTrans_app LG LF β α W e.inv X

end CategoryTheory.Functor.leftDerivedNatIso
