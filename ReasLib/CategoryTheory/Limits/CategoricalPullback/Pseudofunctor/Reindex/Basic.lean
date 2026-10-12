/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Basic Reindexing for Pointwise Categorical Pullbacks

This leaf constructs reindexing functors for pointwise categorical pullbacks and records their
projection and component formulas.
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

/-- The cospan transformation which reindexes the pointwise categorical pullback of two indexed
functors along a base arrow. -/
noncomputable def Pullback.Reindex.transform
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V : C} (f : V ⟶ U) :
    CatCospanTransform (L.app U) (R.app U) (L.app V) (R.app V) :=
  CatCospanTransform.ofIso (L.naturality f).symm (R.naturality f).symm

/-- Reindexing between pointwise categorical pullbacks of two indexed functors. -/
@[stacks 0040 "componentwise reindexing of a categorical pseudo-pullback"]
noncomputable def Pullback.Reindex.functor
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V : C} (f : V ⟶ U) :
    ((L.app U) ⊡ (R.app U)) ⥤ ((L.app V) ⊡ (R.app V)) :=
  CategoricalPullback.map (Pullback.Reindex.transform L R f)

/-- The first projection of pointwise pullback reindexing is the action of the left source
pseudofunctor. -/
noncomputable def Pullback.Reindex.fstIso
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V : C} (f : V ⟶ U) :
    Pullback.Reindex.functor L R f ⋙ π₁ (L.app V) (R.app V) ≅
      π₁ (L.app U) (R.app U) ⋙ (F.map f.op.toLoc).toFunctor :=
  CategoricalPullback.mapFstIso (Pullback.Reindex.transform L R f)

/-- The second projection of pointwise pullback reindexing is the action of the right source
pseudofunctor. -/
noncomputable def Pullback.Reindex.sndIso
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V : C} (f : V ⟶ U) :
    Pullback.Reindex.functor L R f ⋙ π₂ (L.app V) (R.app V) ≅
      π₂ (L.app U) (R.app U) ⋙ (G.map f.op.toLoc).toFunctor :=
  CategoricalPullback.mapSndIso (Pullback.Reindex.transform L R f)

/-- The left object component of pointwise pullback reindexing. -/
@[simp]
theorem Pullback.Reindex.functor.obj.fst
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V : C} (f : V ⟶ U) (P : (L.app U) ⊡ (R.app U)) :
    (Pullback.Reindex.functor L R f |>.obj P).fst =
      (F.map f.op.toLoc).toFunctor.obj P.fst := sorry

/-- The right object component of pointwise pullback reindexing. -/
@[simp]
theorem Pullback.Reindex.functor.obj.snd
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V : C} (f : V ⟶ U) (P : (L.app U) ⊡ (R.app U)) :
    (Pullback.Reindex.functor L R f |>.obj P).snd =
      (G.map f.op.toLoc).toFunctor.obj P.snd := sorry

/-- The structural isomorphism of a reindexed pointwise-pullback object is obtained by applying
the middle pseudofunctor and conjugating by the two indexed-naturality comparisons. -/
@[simp]
theorem Pullback.Reindex.functor.obj.iso
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V : C} (f : V ⟶ U) (P : (L.app U) ⊡ (R.app U)) :
    (Pullback.Reindex.functor L R f |>.obj P).iso =
      (L.naturality f).app P.fst ≪≫
        (H.map (u.map f).op.toLoc).toFunctor.mapIso P.iso ≪≫
        (R.naturality f).symm.app P.snd := sorry

/-- The forward structural map of a reindexed pullback object is obtained by applying the
middle pseudofunctor and the two indexed-naturality comparisons. -/
@[simp]
theorem Pullback.Reindex.functor.obj.iso.hom
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V : C} (f : V ⟶ U) (P : (L.app U) ⊡ (R.app U)) :
    (Pullback.Reindex.functor L R f |>.obj P).iso.hom =
      (L.naturality f).hom.app P.fst ≫
        (H.map (u.map f).op.toLoc).toFunctor.map P.iso.hom ≫
        (R.naturality f).inv.app P.snd := sorry

/-- The inverse structural map of a reindexed pullback object is obtained by applying the
middle pseudofunctor and the inverse indexed-naturality comparisons. -/
@[simp]
theorem Pullback.Reindex.functor.obj.iso.inv
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V : C} (f : V ⟶ U) (P : (L.app U) ⊡ (R.app U)) :
    (Pullback.Reindex.functor L R f |>.obj P).iso.inv =
      (R.naturality f).hom.app P.snd ≫
        (H.map (u.map f).op.toLoc).toFunctor.map P.iso.inv ≫
        (L.naturality f).inv.app P.fst := sorry

/-- The left morphism component of pointwise pullback reindexing. -/
@[simp]
theorem Pullback.Reindex.functor.map.fst
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V : C} (f : V ⟶ U)
    {P Q : (L.app U) ⊡ (R.app U)} (φ : P ⟶ Q) :
    (Pullback.Reindex.functor L R f |>.map φ).fst =
      (F.map f.op.toLoc).toFunctor.map φ.fst := sorry

/-- The right morphism component of pointwise pullback reindexing. -/
@[simp]
theorem Pullback.Reindex.functor.map.snd
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V : C} (f : V ⟶ U)
    {P Q : (L.app U) ⊡ (R.app U)} (φ : P ⟶ Q) :
    (Pullback.Reindex.functor L R f |>.map φ).snd =
      (G.map f.op.toLoc).toFunctor.map φ.snd := sorry

/-- The forward component of the first-projection comparison is the identity. -/
@[simp]
theorem Pullback.Reindex.fstIso.hom.app
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V : C} (f : V ⟶ U) (P : (L.app U) ⊡ (R.app U)) :
    (Pullback.Reindex.fstIso L R f).hom.app P = 𝟙 _ := sorry

/-- The inverse component of the first-projection comparison is the identity. -/
@[simp]
theorem Pullback.Reindex.fstIso.inv.app
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V : C} (f : V ⟶ U) (P : (L.app U) ⊡ (R.app U)) :
    (Pullback.Reindex.fstIso L R f).inv.app P = 𝟙 _ := sorry

/-- The forward component of the second-projection comparison is the identity. -/
@[simp]
theorem Pullback.Reindex.sndIso.hom.app
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V : C} (f : V ⟶ U) (P : (L.app U) ⊡ (R.app U)) :
    (Pullback.Reindex.sndIso L R f).hom.app P = 𝟙 _ := sorry

/-- The inverse component of the second-projection comparison is the identity. -/
@[simp]
theorem Pullback.Reindex.sndIso.inv.app
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V : C} (f : V ⟶ U) (P : (L.app U) ⊡ (R.app U)) :
    (Pullback.Reindex.sndIso L R f).inv.app P = 𝟙 _ := sorry

end Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

end CategoryTheory
