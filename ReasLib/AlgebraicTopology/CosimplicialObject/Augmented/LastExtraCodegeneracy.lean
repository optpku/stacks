/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Augmented.Composition.Pointwise
public import ReasLib.CategoryTheory.Functor.Const.Adjunction

/-!
# Last extra codegeneracies on augmented cosimplicial objects

A last extra codegeneracy contracts the final coface of an augmented cosimplicial object. This
leaf owns the generic structure, its canonical retraction, and the resulting split monomorphism;
homotopical consequences live in the separate `LastExtraCodegeneracy/Homotopy` leaf.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped Simplicial

universe u v u' v'

namespace CategoryTheory.CosimplicialObject.Augmented

variable {C : Type u} [Category.{v} C]

/-- A last extra codegeneracy on an augmented cosimplicial object. It is the covariant dual of
a last extra degeneracy: the distinguished codegeneracy retracts the final coface. -/
@[ext, stacks 0FKS "last extra codegeneracy on an augmented cosimplicial object"]
structure LastExtraCodegeneracy (X : CosimplicialObject.Augmented C) where
  /-- A retraction of the coaugmentation in degree zero. -/
  s' : X.right ^⦋0⦌ ⟶ X.left
  /-- The last extra codegeneracy in every cosimplicial degree. -/
  s : ∀ n : ℕ, X.right ^⦋n + 1⦌ ⟶ X.right ^⦋n⦌
  /-- The degree-zero retraction splits the coaugmentation. -/
  η_comp_s' : X.hom.app ⦋0⦌ ≫ s' = 𝟙 X.left
  /-- The zeroth coface followed by the first extra codegeneracy factors through the
  coaugmentation and its retraction. -/
  δ₀_comp_s₀ : X.right.δ 0 ≫ s 0 = s' ≫ X.hom.app ⦋0⦌
  /-- Every last extra codegeneracy retracts the final coface. -/
  δ_last_comp_s : ∀ n : ℕ, X.right.δ (Fin.last (n + 1)) ≫ s n = 𝟙 _
  /-- Nonfinal cofaces commute with the last extra codegeneracies. -/
  δ_comp_s : ∀ (n : ℕ) (i : Fin (n + 2)),
    X.right.δ i.castSucc ≫ s (n + 1) = s n ≫ X.right.δ i
  /-- Ordinary codegeneracies commute with the last extra codegeneracies. -/
  σ_comp_s : ∀ (n : ℕ) (i : Fin (n + 1)),
    X.right.σ i.castSucc ≫ s n = s (n + 1) ≫ X.right.σ i

namespace LastExtraCodegeneracy

variable {X : CosimplicialObject.Augmented C} (ed : LastExtraCodegeneracy X)

attribute [reassoc] δ₀_comp_s₀ δ_comp_s σ_comp_s
attribute [reassoc (attr := simp)] η_comp_s' δ_last_comp_s

namespace map

variable {D : Type u'} [Category.{v'} D] (F : C ⥤ D)

/-- The mapped degree-zero retraction splits the mapped coaugmentation. -/
@[stacks 0FKS "mapped degree-zero last-extra-codegeneracy retraction"]
theorem η_comp_s' :
    (((CosimplicialObject.Augmented.whiskering C D).obj F).obj X).hom.app ⦋0⦌ ≫
        F.map ed.s' =
      𝟙 (F.obj X.left) := sorry

/-- The mapped initial last-codegeneracy relation. -/
@[stacks 0FKS "mapped initial last-extra-codegeneracy relation"]
theorem δ₀_comp_s₀ :
    (((CosimplicialObject.Augmented.whiskering C D).obj F).obj X).right.δ 0 ≫
        F.map (ed.s 0) =
      F.map ed.s' ≫
        (((CosimplicialObject.Augmented.whiskering C D).obj F).obj X).hom.app ⦋0⦌ := sorry

/-- Mapped last extra codegeneracies still retract the final cofaces. -/
@[stacks 0FKS "mapped final-coface last-extra-codegeneracy relation"]
theorem δ_last_comp_s (n : ℕ) :
    (((CosimplicialObject.Augmented.whiskering C D).obj F).obj X).right.δ
          (Fin.last (n + 1)) ≫ F.map (ed.s n) =
      𝟙 _ := sorry

/-- Mapped last extra codegeneracies commute with nonfinal cofaces. -/
@[stacks 0FKS "mapped coface last-extra-codegeneracy relation"]
theorem δ_comp_s (n : ℕ) (i : Fin (n + 2)) :
    (((CosimplicialObject.Augmented.whiskering C D).obj F).obj X).right.δ i.castSucc ≫
        F.map (ed.s (n + 1)) =
      F.map (ed.s n) ≫
        (((CosimplicialObject.Augmented.whiskering C D).obj F).obj X).right.δ i := sorry

/-- Mapped last extra codegeneracies commute with ordinary codegeneracies. -/
@[stacks 0FKS "mapped codegeneracy last-extra-codegeneracy relation"]
theorem σ_comp_s (n : ℕ) (i : Fin (n + 1)) :
    (((CosimplicialObject.Augmented.whiskering C D).obj F).obj X).right.σ i.castSucc ≫
        F.map (ed.s n) =
      F.map (ed.s (n + 1)) ≫
        (((CosimplicialObject.Augmented.whiskering C D).obj F).obj X).right.σ i := sorry

end map

/-- Last extra codegeneracies are preserved by applying a functor to an augmented cosimplicial
object. -/
@[stacks 0FKS "functoriality of last extra codegeneracies"]
def map {D : Type u'} [Category.{v'} D] (F : C ⥤ D) :
    LastExtraCodegeneracy
      (((CosimplicialObject.Augmented.whiskering C D).obj F).obj X) where
  s' := F.map ed.s'
  s n := F.map (ed.s n)
  η_comp_s' := map.η_comp_s' ed F
  δ₀_comp_s₀ := map.δ₀_comp_s₀ ed F
  δ_last_comp_s := map.δ_last_comp_s ed F
  δ_comp_s := map.δ_comp_s ed F
  σ_comp_s := map.σ_comp_s ed F

/-- The degree-zero retraction of a mapped last extra codegeneracy is obtained by applying the
functor. -/
@[simp, stacks 0FKS "mapped last extra codegeneracy zero-retraction"]
theorem map_s' {D : Type u'} [Category.{v'} D] (F : C ⥤ D) :
    (ed.map F).s' = F.map ed.s' := sorry

/-- The degreewise maps of a mapped last extra codegeneracy are obtained by applying the
functor. -/
@[simp, stacks 0FKS "mapped last extra codegeneracy maps"]
theorem map_s {D : Type u'} [Category.{v'} D] (F : C ⥤ D) (n : ℕ) :
    (ed.map F).s n = F.map (ed.s n) := sorry

namespace app

variable {A : Type u'} [Category.{v'} A]
variable {X : CosimplicialObject.Augmented (A ⥤ C)}
variable (ed : LastExtraCodegeneracy X) (a : A)

/-- The evaluated degree-zero retraction splits the evaluated coaugmentation. -/
@[stacks 0FKS "evaluated degree-zero last-extra-codegeneracy retraction"]
theorem η_comp_s' :
    (CosimplicialObject.Augmented.Pointwise.obj X a).hom.app ⦋0⦌ ≫ ed.s'.app a =
      𝟙 ((CosimplicialObject.Augmented.Pointwise.obj X a).left) := sorry

/-- The initial last-codegeneracy relation holds after evaluation. -/
@[stacks 0FKS "evaluated initial last-extra-codegeneracy relation"]
theorem δ₀_comp_s₀ :
    (CosimplicialObject.Augmented.Pointwise.obj X a).right.δ 0 ≫ (ed.s 0).app a =
      ed.s'.app a ≫ (CosimplicialObject.Augmented.Pointwise.obj X a).hom.app ⦋0⦌ := sorry

/-- Evaluated last extra codegeneracies still retract the final cofaces. -/
@[stacks 0FKS "evaluated final-coface last-extra-codegeneracy relation"]
theorem δ_last_comp_s (n : ℕ) :
    (CosimplicialObject.Augmented.Pointwise.obj X a).right.δ
          (Fin.last (n + 1)) ≫ (ed.s n).app a =
      𝟙 _ := sorry

/-- Evaluated last extra codegeneracies commute with nonfinal cofaces. -/
@[stacks 0FKS "evaluated coface last-extra-codegeneracy relation"]
theorem δ_comp_s (n : ℕ) (i : Fin (n + 2)) :
    (CosimplicialObject.Augmented.Pointwise.obj X a).right.δ i.castSucc ≫
        (ed.s (n + 1)).app a =
      (ed.s n).app a ≫
        (CosimplicialObject.Augmented.Pointwise.obj X a).right.δ i := sorry

/-- Evaluated last extra codegeneracies commute with ordinary codegeneracies. -/
@[stacks 0FKS "evaluated codegeneracy last-extra-codegeneracy relation"]
theorem σ_comp_s (n : ℕ) (i : Fin (n + 1)) :
    (CosimplicialObject.Augmented.Pointwise.obj X a).right.σ i.castSucc ≫
        (ed.s n).app a =
      (ed.s (n + 1)).app a ≫
        (CosimplicialObject.Augmented.Pointwise.obj X a).right.σ i := sorry

end app

/-- Evaluate a last extra codegeneracy on a functor-valued augmented cosimplicial object at one
object. -/
@[stacks 0FKS "objectwise evaluation of a last extra codegeneracy"]
def app {A : Type u'} [Category.{v'} A]
    {X : CosimplicialObject.Augmented (A ⥤ C)}
    (ed : LastExtraCodegeneracy X) (a : A) :
    LastExtraCodegeneracy (CosimplicialObject.Augmented.Pointwise.obj X a) where
  s' := ed.s'.app a
  s n := (ed.s n).app a
  η_comp_s' := app.η_comp_s' ed a
  δ₀_comp_s₀ := app.δ₀_comp_s₀ ed a
  δ_last_comp_s := app.δ_last_comp_s ed a
  δ_comp_s := app.δ_comp_s ed a
  σ_comp_s := app.σ_comp_s ed a

/-- The degree-zero retraction of an evaluated last extra codegeneracy is evaluated
pointwise. -/
@[simp, stacks 0FKS "evaluated last extra codegeneracy zero-retraction"]
theorem app_s' {A : Type u'} [Category.{v'} A]
    {X : CosimplicialObject.Augmented (A ⥤ C)}
    (ed : LastExtraCodegeneracy X) (a : A) :
    (ed.app a).s' = ed.s'.app a := sorry

/-- Each map of an evaluated last extra codegeneracy is evaluated pointwise. -/
@[simp, stacks 0FKS "evaluated last extra codegeneracy maps"]
theorem app_s {A : Type u'} [Category.{v'} A]
    {X : CosimplicialObject.Augmented (A ⥤ C)}
    (ed : LastExtraCodegeneracy X) (a : A) (n : ℕ) :
    (ed.app a).s n = (ed.s n).app a := sorry

namespace ofIso

variable {Y : CosimplicialObject.Augmented C} (e : X ≅ Y)

/-- The transported degree-zero retraction splits the target coaugmentation. -/
@[stacks 0FKS "transported degree-zero last-extra-codegeneracy retraction"]
theorem η_comp_s' :
    Y.hom.app ⦋0⦌ ≫
        ((CosimplicialObject.Augmented.drop.mapIso e).inv.app ⦋0⦌ ≫ ed.s' ≫
          (CosimplicialObject.Augmented.point.mapIso e).hom) =
      𝟙 Y.left := sorry

/-- The initial last-codegeneracy relation is preserved by transport. -/
@[stacks 0FKS "transported initial last-extra-codegeneracy relation"]
theorem δ₀_comp_s₀ :
    Y.right.δ 0 ≫
        ((CosimplicialObject.Augmented.drop.mapIso e).inv.app ⦋1⦌ ≫ ed.s 0 ≫
          (CosimplicialObject.Augmented.drop.mapIso e).hom.app ⦋0⦌) =
      ((CosimplicialObject.Augmented.drop.mapIso e).inv.app ⦋0⦌ ≫ ed.s' ≫
          (CosimplicialObject.Augmented.point.mapIso e).hom) ≫
        Y.hom.app ⦋0⦌ := sorry

/-- Transported last extra codegeneracies still retract the final cofaces. -/
@[stacks 0FKS "transported final-coface last-extra-codegeneracy relation"]
theorem δ_last_comp_s (n : ℕ) :
    Y.right.δ (Fin.last (n + 1)) ≫
        ((CosimplicialObject.Augmented.drop.mapIso e).inv.app ⦋n + 1⦌ ≫ ed.s n ≫
          (CosimplicialObject.Augmented.drop.mapIso e).hom.app ⦋n⦌) =
      𝟙 _ := sorry

/-- Transported last extra codegeneracies commute with nonfinal cofaces. -/
@[stacks 0FKS "transported coface last-extra-codegeneracy relation"]
theorem δ_comp_s (n : ℕ) (i : Fin (n + 2)) :
    Y.right.δ i.castSucc ≫
        ((CosimplicialObject.Augmented.drop.mapIso e).inv.app ⦋n + 2⦌ ≫
          ed.s (n + 1) ≫
            (CosimplicialObject.Augmented.drop.mapIso e).hom.app ⦋n + 1⦌) =
      ((CosimplicialObject.Augmented.drop.mapIso e).inv.app ⦋n + 1⦌ ≫ ed.s n ≫
          (CosimplicialObject.Augmented.drop.mapIso e).hom.app ⦋n⦌) ≫
        Y.right.δ i := sorry

/-- Transported last extra codegeneracies commute with ordinary codegeneracies. -/
@[stacks 0FKS "transported codegeneracy last-extra-codegeneracy relation"]
theorem σ_comp_s (n : ℕ) (i : Fin (n + 1)) :
    Y.right.σ i.castSucc ≫
        ((CosimplicialObject.Augmented.drop.mapIso e).inv.app ⦋n + 1⦌ ≫ ed.s n ≫
          (CosimplicialObject.Augmented.drop.mapIso e).hom.app ⦋n⦌) =
      ((CosimplicialObject.Augmented.drop.mapIso e).inv.app ⦋n + 2⦌ ≫
          ed.s (n + 1) ≫
            (CosimplicialObject.Augmented.drop.mapIso e).hom.app ⦋n + 1⦌) ≫
        Y.right.σ i := sorry

end ofIso

/-- Transport a last extra codegeneracy across an isomorphism of augmented cosimplicial
objects. -/
@[stacks 0FKS "isomorphism invariance of last extra codegeneracies"]
def ofIso {Y : CosimplicialObject.Augmented C} (e : X ≅ Y)
    (ed : LastExtraCodegeneracy X) : LastExtraCodegeneracy Y where
  s' := (CosimplicialObject.Augmented.drop.mapIso e).inv.app ⦋0⦌ ≫ ed.s' ≫
    (CosimplicialObject.Augmented.point.mapIso e).hom
  s n := (CosimplicialObject.Augmented.drop.mapIso e).inv.app ⦋n + 1⦌ ≫ ed.s n ≫
    (CosimplicialObject.Augmented.drop.mapIso e).hom.app ⦋n⦌
  η_comp_s' := ofIso.η_comp_s' ed e
  δ₀_comp_s₀ := ofIso.δ₀_comp_s₀ ed e
  δ_last_comp_s := ofIso.δ_last_comp_s ed e
  δ_comp_s := ofIso.δ_comp_s ed e
  σ_comp_s := ofIso.σ_comp_s ed e

/-- The degree-zero retraction of a transported last extra codegeneracy is conjugated by the
point and cosimplicial isomorphisms. -/
@[simp, stacks 0FKS "transported last extra codegeneracy zero-retraction"]
theorem ofIso_s' {Y : CosimplicialObject.Augmented C} (e : X ≅ Y)
    (ed : LastExtraCodegeneracy X) :
    (ofIso e ed).s' =
      (CosimplicialObject.Augmented.drop.mapIso e).inv.app ⦋0⦌ ≫ ed.s' ≫
        (CosimplicialObject.Augmented.point.mapIso e).hom := sorry

/-- The degreewise maps of a transported last extra codegeneracy are conjugated by the
cosimplicial isomorphism. -/
@[simp, stacks 0FKS "transported last extra codegeneracy maps"]
theorem ofIso_s {Y : CosimplicialObject.Augmented C} (e : X ≅ Y)
    (ed : LastExtraCodegeneracy X) (n : ℕ) :
    (ofIso e ed).s n =
      (CosimplicialObject.Augmented.drop.mapIso e).inv.app ⦋n + 1⦌ ≫ ed.s n ≫
        (CosimplicialObject.Augmented.drop.mapIso e).hom.app ⦋n⦌ := sorry

/-- Transport along the identity isomorphism preserves a last extra codegeneracy. -/
@[simp, stacks 0FKS "identity transport of a last extra codegeneracy"]
theorem ofIso_refl : ofIso (Iso.refl X) ed = ed := sorry

/-- Transporting a last extra codegeneracy across two isomorphisms agrees with transport across
their composite. -/
@[stacks 0FKS "composition of last extra codegeneracy transports"]
theorem ofIso_trans {Y Z : CosimplicialObject.Augmented C}
    (e : X ≅ Y) (f : Y ≅ Z) :
    ofIso (e ≪≫ f) ed = ofIso f (ofIso e ed) := sorry

/-- The cosimplicial retraction generated by the degree-zero retraction of a last extra
codegeneracy. -/
@[stacks 0FKS "cosimplicial retraction from a last extra codegeneracy"]
def retraction : X.right ⟶ (CosimplicialObject.const C).obj X.left :=
  SimplexCategory.isTerminalZero.toConst ed.s'

/-- Every component of the retraction is the unique map to degree zero followed by the chosen
degree-zero retraction. -/
@[simp, stacks 0FKS "component of the last-extra-codegeneracy retraction"]
theorem retraction.app (Δ : SimplexCategory) :
    ed.retraction.app Δ =
      X.right.map (SimplexCategory.isTerminalZero.from Δ) ≫ ed.s' := sorry

/-- The degree-zero component of the cosimplicial retraction is its defining retraction. -/
@[simp, stacks 0FKS "degree-zero last-extra-codegeneracy retraction"]
theorem retraction.app_zero : ed.retraction.app ⦋0⦌ = ed.s' := sorry

/-- Applying a functor to a last extra codegeneracy commutes with forming the canonical
retraction. -/
@[stacks 0FKS "functoriality of the last-extra-codegeneracy retraction"]
theorem map_retraction {D : Type u'} [Category.{v'} D] (F : C ⥤ D) :
    (ed.map F).retraction =
      Functor.whiskerRight ed.retraction F ≫
        (Functor.constComp SimplexCategory X.left F).hom := sorry

/-- Componentwise, the canonical retraction of a mapped last extra codegeneracy is obtained by
applying the functor. -/
@[simp, stacks 0FKS "component of a mapped last-extra-codegeneracy retraction"]
theorem map_retraction_app {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    (Δ : SimplexCategory) :
    (ed.map F).retraction.app Δ = F.map (ed.retraction.app Δ) := sorry

/-- Evaluating a functor-valued last extra codegeneracy commutes with forming the canonical
retraction. -/
@[stacks 0FKS "pointwise evaluation of the last-extra-codegeneracy retraction"]
theorem app_retraction {A : Type u'} [Category.{v'} A]
    {X : CosimplicialObject.Augmented (A ⥤ C)}
    (ed : LastExtraCodegeneracy X) (a : A) :
    (ed.app a).retraction = NatTrans.flipApp ed.retraction a := sorry

/-- Components of the canonical retraction evaluate pointwise. -/
@[simp, stacks 0FKS "component of an evaluated last-extra-codegeneracy retraction"]
theorem app_retraction_app {A : Type u'} [Category.{v'} A]
    {X : CosimplicialObject.Augmented (A ⥤ C)}
    (ed : LastExtraCodegeneracy X) (a : A) (Δ : SimplexCategory) :
    (ed.app a).retraction.app Δ = (ed.retraction.app Δ).app a := sorry

/-- Transporting a last extra codegeneracy across an isomorphism conjugates its canonical
retraction by the induced point and cosimplicial isomorphisms. -/
@[stacks 0FKS "transported last-extra-codegeneracy retraction"]
theorem ofIso_retraction {Y : CosimplicialObject.Augmented C} (e : X ≅ Y) :
    (ofIso e ed).retraction =
      (CosimplicialObject.Augmented.drop.mapIso e).inv ≫ ed.retraction ≫
        (CosimplicialObject.const C).map
          (CosimplicialObject.Augmented.point.mapIso e).hom := sorry

/-- The coaugmentation followed by the retraction supplied by a last extra codegeneracy is the
identity of the constant cosimplicial object. -/
@[simp, stacks 0FKS "coaugmentation-retraction identity"]
theorem hom_comp_retraction :
    X.hom ≫ ed.retraction = 𝟙 ((CosimplicialObject.const C).obj X.left) := sorry

/-- A last extra codegeneracy canonically exhibits its coaugmentation as a split monomorphism. -/
@[stacks 0FKS "split monomorphism from a last extra codegeneracy"]
def splitMono : SplitMono X.hom where
  retraction := ed.retraction
  id := ed.hom_comp_retraction

end LastExtraCodegeneracy

end CategoryTheory.CosimplicialObject.Augmented
