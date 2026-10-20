/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Reindex.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity Comparison for Pointwise Pullback Reindexing

This leaf constructs the objectwise and natural identity comparisons for reindexing pointwise
categorical pullbacks.
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

/-- Compatibility of the source-pseudofunctor identity comparisons with the structural
isomorphism of identity pointwise-pullback reindexing. -/
theorem Pullback.Reindex.mapIdIsoApp.w
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (U : C) (P : (L.app U) ⊡ (R.app U)) :
    (L.app U).map
          ((Cat.Hom.toNatIso (F.mapIdOp U)).app P.fst).hom ≫
        P.iso.hom =
      (Pullback.Reindex.functor L R (𝟙 U) |>.obj P).iso.hom ≫
        (R.app U).map
          ((Cat.Hom.toNatIso (G.mapIdOp U)).app P.snd).hom := sorry

/-- The objectwise comparison from identity reindexing to the original pointwise-pullback
object. -/
noncomputable def Pullback.Reindex.mapIdIsoApp
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (U : C) (P : (L.app U) ⊡ (R.app U)) :
    (Pullback.Reindex.functor L R (𝟙 U)).obj P ≅ P :=
  CategoricalPullback.mkIso
    ((Cat.Hom.toNatIso (F.mapIdOp U)).app P.fst)
    ((Cat.Hom.toNatIso (G.mapIdOp U)).app P.snd)
    (Pullback.Reindex.mapIdIsoApp.w L R U P)

/-- The first component of the forward objectwise identity comparison is the left
pseudofunctor identity comparison. -/
@[simp]
theorem Pullback.Reindex.mapIdIsoApp.hom.fst
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (U : C) (P : (L.app U) ⊡ (R.app U)) :
    (Pullback.Reindex.mapIdIsoApp L R U P).hom.fst =
      (F.mapIdOp U).hom.toNatTrans.app P.fst := sorry

/-- The second component of the forward objectwise identity comparison is the right
pseudofunctor identity comparison. -/
@[simp]
theorem Pullback.Reindex.mapIdIsoApp.hom.snd
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (U : C) (P : (L.app U) ⊡ (R.app U)) :
    (Pullback.Reindex.mapIdIsoApp L R U P).hom.snd =
      (G.mapIdOp U).hom.toNatTrans.app P.snd := sorry

/-- The first component of the inverse objectwise identity comparison is the inverse left
pseudofunctor identity comparison. -/
@[simp]
theorem Pullback.Reindex.mapIdIsoApp.inv.fst
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (U : C) (P : (L.app U) ⊡ (R.app U)) :
    (Pullback.Reindex.mapIdIsoApp L R U P).inv.fst =
      (F.mapIdOp U).inv.toNatTrans.app P.fst := sorry

/-- The second component of the inverse objectwise identity comparison is the inverse right
pseudofunctor identity comparison. -/
@[simp]
theorem Pullback.Reindex.mapIdIsoApp.inv.snd
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (U : C) (P : (L.app U) ⊡ (R.app U)) :
    (Pullback.Reindex.mapIdIsoApp L R U P).inv.snd =
      (G.mapIdOp U).inv.toNatTrans.app P.snd := sorry

/-- The forward objectwise identity comparisons are natural. -/
theorem Pullback.Reindex.mapIdIsoApp.naturality.hom
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (U : C) {P Q : (L.app U) ⊡ (R.app U)} (φ : P ⟶ Q) :
    (Pullback.Reindex.functor L R (𝟙 U)).map φ ≫
        (Pullback.Reindex.mapIdIsoApp L R U Q).hom =
      (Pullback.Reindex.mapIdIsoApp L R U P).hom ≫ φ := sorry

/-- The inverse objectwise identity comparisons are natural. -/
theorem Pullback.Reindex.mapIdIsoApp.naturality.inv
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (U : C) {P Q : (L.app U) ⊡ (R.app U)} (φ : P ⟶ Q) :
    φ ≫ (Pullback.Reindex.mapIdIsoApp L R U Q).inv =
      (Pullback.Reindex.mapIdIsoApp L R U P).inv ≫
        (Pullback.Reindex.functor L R (𝟙 U)).map φ := sorry

/-- Identity pointwise-pullback reindexing is naturally isomorphic to the identity functor. -/
@[stacks 0040 "identity comparison for pointwise categorical pseudo-pullback reindexing"]
noncomputable def Pullback.Reindex.mapIdIso
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (U : C) :
    Pullback.Reindex.functor L R (𝟙 U) ≅ 𝟭 ((L.app U) ⊡ (R.app U)) :=
  NatIso.ofComponents
    (Pullback.Reindex.mapIdIsoApp L R U)
    (fun φ ↦ Pullback.Reindex.mapIdIsoApp.naturality.hom L R U φ)

/-- The first component of the forward identity-reindexing comparison is the left
pseudofunctor identity comparison. -/
@[simp]
theorem Pullback.Reindex.mapIdIso.hom.app.fst
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (U : C) (P : (L.app U) ⊡ (R.app U)) :
    ((Pullback.Reindex.mapIdIso L R U).hom.app P).fst =
      (F.mapIdOp U).hom.toNatTrans.app P.fst := sorry

/-- The second component of the forward identity-reindexing comparison is the right
pseudofunctor identity comparison. -/
@[simp]
theorem Pullback.Reindex.mapIdIso.hom.app.snd
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (U : C) (P : (L.app U) ⊡ (R.app U)) :
    ((Pullback.Reindex.mapIdIso L R U).hom.app P).snd =
      (G.mapIdOp U).hom.toNatTrans.app P.snd := sorry

/-- The first component of the inverse identity-reindexing comparison is the inverse left
pseudofunctor identity comparison. -/
@[simp]
theorem Pullback.Reindex.mapIdIso.inv.app.fst
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (U : C) (P : (L.app U) ⊡ (R.app U)) :
    ((Pullback.Reindex.mapIdIso L R U).inv.app P).fst =
      (F.mapIdOp U).inv.toNatTrans.app P.fst := sorry

/-- The second component of the inverse identity-reindexing comparison is the inverse right
pseudofunctor identity comparison. -/
@[simp]
theorem Pullback.Reindex.mapIdIso.inv.app.snd
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (U : C) (P : (L.app U) ⊡ (R.app U)) :
    ((Pullback.Reindex.mapIdIso L R U).inv.app P).snd =
      (G.mapIdOp U).inv.toNatTrans.app P.snd := sorry

end Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

end CategoryTheory
