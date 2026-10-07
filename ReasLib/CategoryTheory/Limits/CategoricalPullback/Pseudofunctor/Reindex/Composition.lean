module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Reindex.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition Comparison for Pointwise Pullback Reindexing

This leaf constructs the objectwise and natural composition comparisons for reindexing
pointwise categorical pullbacks.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback Opposite
open scoped CategoricalPullback CategoryTheory.Bicategory

universe uC vC uD vD uF vF uG vG uH vH

namespace CategoryTheory

namespace Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {u : C ⥤ D}
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF}}
variable {G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vG, uG}}
variable {H : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vH, uH}}

/-- Compatibility of the two source-pseudofunctor composition comparisons with the structural
isomorphisms of direct and successive pointwise-pullback reindexing. -/
theorem Pullback.Reindex.mapCompIsoApp.w
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : (L.app U) ⊡ (R.app U)) :
    (L.app W).map
          ((Cat.Hom.toNatIso (F.mapCompOp f g)).app P.fst).hom ≫
        ((Pullback.Reindex.functor L R f ⋙ Pullback.Reindex.functor L R g).obj P).iso.hom =
      (Pullback.Reindex.functor L R (g ≫ f) |>.obj P).iso.hom ≫
        (R.app W).map
          ((Cat.Hom.toNatIso (G.mapCompOp f g)).app P.snd).hom := sorry

/-- The objectwise comparison from direct pointwise-pullback reindexing along `g ≫ f` to
successive reindexing along `f` and `g`. -/
noncomputable def Pullback.Reindex.mapCompIsoApp
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : (L.app U) ⊡ (R.app U)) :
    (Pullback.Reindex.functor L R (g ≫ f)).obj P ≅
      (Pullback.Reindex.functor L R f ⋙ Pullback.Reindex.functor L R g).obj P :=
  CategoricalPullback.mkIso
    ((Cat.Hom.toNatIso (F.mapCompOp f g)).app P.fst)
    ((Cat.Hom.toNatIso (G.mapCompOp f g)).app P.snd)
    (Pullback.Reindex.mapCompIsoApp.w L R f g P)

/-- The first component of the forward objectwise composition comparison is the composition
comparison of the left source pseudofunctor. -/
@[simp]
theorem Pullback.Reindex.mapCompIsoApp.hom.fst
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : (L.app U) ⊡ (R.app U)) :
    (Pullback.Reindex.mapCompIsoApp L R f g P).hom.fst =
      (F.mapCompOp f g).hom.toNatTrans.app P.fst := sorry

/-- The second component of the forward objectwise composition comparison is the composition
comparison of the right source pseudofunctor. -/
@[simp]
theorem Pullback.Reindex.mapCompIsoApp.hom.snd
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : (L.app U) ⊡ (R.app U)) :
    (Pullback.Reindex.mapCompIsoApp L R f g P).hom.snd =
      (G.mapCompOp f g).hom.toNatTrans.app P.snd := sorry

/-- The first component of the inverse objectwise composition comparison is the inverse
composition comparison of the left source pseudofunctor. -/
@[simp]
theorem Pullback.Reindex.mapCompIsoApp.inv.fst
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : (L.app U) ⊡ (R.app U)) :
    (Pullback.Reindex.mapCompIsoApp L R f g P).inv.fst =
      (F.mapCompOp f g).inv.toNatTrans.app P.fst := sorry

/-- The second component of the inverse objectwise composition comparison is the inverse
composition comparison of the right source pseudofunctor. -/
@[simp]
theorem Pullback.Reindex.mapCompIsoApp.inv.snd
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : (L.app U) ⊡ (R.app U)) :
    (Pullback.Reindex.mapCompIsoApp L R f g P).inv.snd =
      (G.mapCompOp f g).inv.toNatTrans.app P.snd := sorry

/-- The forward objectwise pointwise-pullback composition comparisons are natural. -/
theorem Pullback.Reindex.mapCompIsoApp.naturality.hom
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    {P Q : (L.app U) ⊡ (R.app U)} (φ : P ⟶ Q) :
    (Pullback.Reindex.functor L R (g ≫ f)).map φ ≫
        (Pullback.Reindex.mapCompIsoApp L R f g Q).hom =
      (Pullback.Reindex.mapCompIsoApp L R f g P).hom ≫
        (Pullback.Reindex.functor L R f ⋙ Pullback.Reindex.functor L R g).map φ := sorry

/-- The inverse objectwise pointwise-pullback composition comparisons are natural. -/
theorem Pullback.Reindex.mapCompIsoApp.naturality.inv
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    {P Q : (L.app U) ⊡ (R.app U)} (φ : P ⟶ Q) :
    (Pullback.Reindex.functor L R f ⋙ Pullback.Reindex.functor L R g).map φ ≫
        (Pullback.Reindex.mapCompIsoApp L R f g Q).inv =
      (Pullback.Reindex.mapCompIsoApp L R f g P).inv ≫
        (Pullback.Reindex.functor L R (g ≫ f)).map φ := sorry

/-- Direct and successive pointwise-pullback reindexing are naturally isomorphic. -/
@[stacks 0040 "composition comparison for pointwise categorical pseudo-pullback reindexing"]
noncomputable def Pullback.Reindex.mapCompIso
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    Pullback.Reindex.functor L R (g ≫ f) ≅
      Pullback.Reindex.functor L R f ⋙ Pullback.Reindex.functor L R g :=
  NatIso.ofComponents
    (Pullback.Reindex.mapCompIsoApp L R f g)
    (fun φ ↦ Pullback.Reindex.mapCompIsoApp.naturality.hom L R f g φ)

/-- The first component of the forward pointwise-pullback composition comparison is the
composition comparison of the left source pseudofunctor. -/
@[simp]
theorem Pullback.Reindex.mapCompIso.hom.app.fst
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : (L.app U) ⊡ (R.app U)) :
    ((Pullback.Reindex.mapCompIso L R f g).hom.app P).fst =
      (F.mapCompOp f g).hom.toNatTrans.app P.fst := sorry

/-- The second component of the forward pointwise-pullback composition comparison is the
composition comparison of the right source pseudofunctor. -/
@[simp]
theorem Pullback.Reindex.mapCompIso.hom.app.snd
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : (L.app U) ⊡ (R.app U)) :
    ((Pullback.Reindex.mapCompIso L R f g).hom.app P).snd =
      (G.mapCompOp f g).hom.toNatTrans.app P.snd := sorry

/-- The first component of the inverse pointwise-pullback composition comparison is the inverse
composition comparison of the left source pseudofunctor. -/
@[simp]
theorem Pullback.Reindex.mapCompIso.inv.app.fst
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : (L.app U) ⊡ (R.app U)) :
    ((Pullback.Reindex.mapCompIso L R f g).inv.app P).fst =
      (F.mapCompOp f g).inv.toNatTrans.app P.fst := sorry

/-- The second component of the inverse pointwise-pullback composition comparison is the inverse
composition comparison of the right source pseudofunctor. -/
@[simp]
theorem Pullback.Reindex.mapCompIso.inv.app.snd
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : (L.app U) ⊡ (R.app U)) :
    ((Pullback.Reindex.mapCompIso L R f g).inv.app P).snd =
      (G.mapCompOp f g).inv.toNatTrans.app P.snd := sorry

end Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

end CategoryTheory
