/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.FromZero
public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.Composition.Pointwise
public import ReasLib.AlgebraicTopology.SimplicialObject.DeltaLastIter

/-!
# Last extra degeneracies on augmented simplicial objects

A last extra degeneracy is the order-reversed analogue of Mathlib's
`SimplicialObject.Augmented.ExtraDegeneracy`: its distinguished face is the final face, and all
other face and degeneracy indices are included with `Fin.castSucc`.  Keeping the two conventions
as separate structures prevents endpoint reversals from being hidden in downstream statements.
-/

@[expose] public section

open CategoryTheory
open Opposite
open scoped Simplicial

universe u v u' v'

namespace CategoryTheory.SimplicialObject.Augmented

variable {C : Type u} [Category.{v} C]

/-- A last extra degeneracy on an augmented simplicial object.  It behaves formally as an extra
degeneracy appended after the ordinary degeneracies. -/
@[ext, stacks 08ND "last extra degeneracy on an augmented simplicial object"]
structure LastExtraDegeneracy (X : SimplicialObject.Augmented C) where
  /-- A section of the augmentation in degree zero. -/
  s' : X.right ⟶ X.left _⦋0⦌
  /-- The last extra degeneracy in every simplicial degree. -/
  s : ∀ n : ℕ, X.left _⦋n⦌ ⟶ X.left _⦋n + 1⦌
  /-- The degree-zero map is a section of the augmentation. -/
  s'_comp_ε : s' ≫ X.hom.app (op ⦋0⦌) = 𝟙 X.right
  /-- The first last extra degeneracy followed by the zeroth face factors through the
  augmentation and its section. -/
  s₀_comp_δ₀ : s 0 ≫ X.left.δ 0 = X.hom.app (op ⦋0⦌) ≫ s'
  /-- Each last extra degeneracy is a section of the final face. -/
  s_comp_δ_last : ∀ n : ℕ, s n ≫ X.left.δ (Fin.last (n + 1)) = 𝟙 _
  /-- Last extra degeneracies commute with all nonfinal faces. -/
  s_comp_δ : ∀ (n : ℕ) (i : Fin (n + 2)),
    s (n + 1) ≫ X.left.δ i.castSucc = X.left.δ i ≫ s n
  /-- Last extra degeneracies commute with the ordinary degeneracies. -/
  s_comp_σ : ∀ (n : ℕ) (i : Fin (n + 1)),
    s n ≫ X.left.σ i.castSucc = X.left.σ i ≫ s (n + 1)

namespace LastExtraDegeneracy

variable {X : SimplicialObject.Augmented C} (ed : LastExtraDegeneracy X)

attribute [reassoc] s₀_comp_δ₀ s_comp_δ s_comp_σ
attribute [reassoc (attr := simp)] s'_comp_ε s_comp_δ_last

namespace map

variable {D : Type u'} [Category.{v'} D] (F : C ⥤ D)

/-- The mapped degree-zero section is a section of the mapped augmentation. -/
theorem s'_comp_ε :
    F.map ed.s' ≫
        (((SimplicialObject.Augmented.whiskering C D).obj F).obj X).hom.app (op ⦋0⦌) =
      𝟙 (F.obj X.right) := by
  set_option backward.isDefEq.respectTransparency false in
    change F.map ed.s' ≫ (F.map (X.hom.app (op ⦋0⦌)) ≫ 𝟙 _) = _
    simpa only [Functor.map_comp, Functor.map_id, Category.comp_id] using
      congrArg F.map ed.s'_comp_ε

/-- The mapped initial last-degeneracy relation. -/
theorem s₀_comp_δ₀ :
    F.map (ed.s 0) ≫
        (((SimplicialObject.Augmented.whiskering C D).obj F).obj X).left.δ 0 =
      (((SimplicialObject.Augmented.whiskering C D).obj F).obj X).hom.app (op ⦋0⦌) ≫
        F.map ed.s' := by
  set_option backward.isDefEq.respectTransparency false in
    change F.map (ed.s 0) ≫ F.map (X.left.δ 0) =
      (F.map (X.hom.app (op ⦋0⦌)) ≫ 𝟙 _) ≫ F.map ed.s'
    simpa only [Functor.map_comp, Category.comp_id] using
      congrArg F.map ed.s₀_comp_δ₀

/-- The mapped last extra degeneracies remain sections of the final faces. -/
theorem s_comp_δ_last (n : ℕ) :
    F.map (ed.s n) ≫
        (((SimplicialObject.Augmented.whiskering C D).obj F).obj X).left.δ
          (Fin.last (n + 1)) =
      𝟙 _ := by
  change F.map (ed.s n) ≫ F.map (X.left.δ (Fin.last (n + 1))) = _
  simpa only [Functor.map_comp, Functor.map_id] using
    congrArg F.map (ed.s_comp_δ_last n)

/-- The mapped last extra degeneracies commute with nonfinal faces. -/
theorem s_comp_δ (n : ℕ) (i : Fin (n + 2)) :
    F.map (ed.s (n + 1)) ≫
        (((SimplicialObject.Augmented.whiskering C D).obj F).obj X).left.δ i.castSucc =
      (((SimplicialObject.Augmented.whiskering C D).obj F).obj X).left.δ i ≫
        F.map (ed.s n) := by
  change F.map (ed.s (n + 1)) ≫ F.map (X.left.δ i.castSucc) =
    F.map (X.left.δ i) ≫ F.map (ed.s n)
  simpa only [Functor.map_comp] using congrArg F.map (ed.s_comp_δ n i)

/-- The mapped last extra degeneracies commute with degeneracies. -/
theorem s_comp_σ (n : ℕ) (i : Fin (n + 1)) :
    F.map (ed.s n) ≫
        (((SimplicialObject.Augmented.whiskering C D).obj F).obj X).left.σ i.castSucc =
      (((SimplicialObject.Augmented.whiskering C D).obj F).obj X).left.σ i ≫
        F.map (ed.s (n + 1)) := by
  change F.map (ed.s n) ≫ F.map (X.left.σ i.castSucc) =
    F.map (X.left.σ i) ≫ F.map (ed.s (n + 1))
  simpa only [Functor.map_comp] using congrArg F.map (ed.s_comp_σ n i)

end map

/-- Last extra degeneracies are preserved by applying a functor to an augmented simplicial
object. -/
@[stacks 08ND "functoriality of last extra degeneracies"]
def map (ed : LastExtraDegeneracy X) {D : Type u'} [Category.{v'} D] (F : C ⥤ D) :
    LastExtraDegeneracy (((SimplicialObject.Augmented.whiskering C D).obj F).obj X) where
  s' := F.map ed.s'
  s n := F.map (ed.s n)
  s'_comp_ε := map.s'_comp_ε ed F
  s₀_comp_δ₀ := map.s₀_comp_δ₀ ed F
  s_comp_δ_last := map.s_comp_δ_last ed F
  s_comp_δ := map.s_comp_δ ed F
  s_comp_σ := map.s_comp_σ ed F

/-- The degree-zero section of the image of a last extra degeneracy is obtained by applying the
functor. -/
@[simp, stacks 08ND "mapped last extra degeneracy zero-section"]
theorem map_s' {D : Type u'} [Category.{v'} D] (F : C ⥤ D) :
    (ed.map F).s' = F.map ed.s' := rfl

/-- The degreewise maps of the image of a last extra degeneracy are obtained by applying the
functor. -/
@[simp, stacks 08ND "mapped last extra degeneracy maps"]
theorem map_s {D : Type u'} [Category.{v'} D] (F : C ⥤ D) (n : ℕ) :
    (ed.map F).s n = F.map (ed.s n) := rfl

namespace app

variable {A : Type u'} [Category.{v'} A]
variable {X : SimplicialObject.Augmented (A ⥤ C)}
variable (ed : LastExtraDegeneracy X) (a : A)

/-- The evaluated zero-section is a section of the evaluated augmentation. -/
theorem s'_comp_ε :
    ed.s'.app a ≫ (SimplicialObject.Augmented.Pointwise.obj X a).hom.app (op ⦋0⦌) =
      𝟙 ((SimplicialObject.Augmented.Pointwise.obj X a).right) := by
  change ed.s'.app a ≫ (X.hom.app (op ⦋0⦌)).app a = 𝟙 (X.right.obj a)
  simpa only [NatTrans.comp_app, NatTrans.id_app] using
    congrArg (fun f => f.app a) ed.s'_comp_ε

/-- The initial face relation for a last extra degeneracy holds after evaluation. -/
theorem s₀_comp_δ₀ :
    (ed.s 0).app a ≫ (SimplicialObject.Augmented.Pointwise.obj X a).left.δ 0 =
      (SimplicialObject.Augmented.Pointwise.obj X a).hom.app (op ⦋0⦌) ≫
        ed.s'.app a := by
  change (ed.s 0).app a ≫ (X.left.δ 0).app a =
    (X.hom.app (op ⦋0⦌)).app a ≫ ed.s'.app a
  simpa only [NatTrans.comp_app] using
    congrArg (fun f => f.app a) ed.s₀_comp_δ₀

/-- Evaluated last extra degeneracies remain sections of the final faces. -/
theorem s_comp_δ_last (n : ℕ) :
    (ed.s n).app a ≫
        (SimplicialObject.Augmented.Pointwise.obj X a).left.δ (Fin.last (n + 1)) =
      𝟙 _ := by
  change (ed.s n).app a ≫ (X.left.δ (Fin.last (n + 1))).app a =
    𝟙 ((X.left _⦋n⦌).obj a)
  simpa only [NatTrans.comp_app, NatTrans.id_app] using
    congrArg (fun f => f.app a) (ed.s_comp_δ_last n)

/-- Evaluated last extra degeneracies commute with all nonfinal faces. -/
theorem s_comp_δ (n : ℕ) (i : Fin (n + 2)) :
    (ed.s (n + 1)).app a ≫
        (SimplicialObject.Augmented.Pointwise.obj X a).left.δ i.castSucc =
      (SimplicialObject.Augmented.Pointwise.obj X a).left.δ i ≫ (ed.s n).app a := by
  change (ed.s (n + 1)).app a ≫ (X.left.δ i.castSucc).app a =
    (X.left.δ i).app a ≫ (ed.s n).app a
  simpa only [NatTrans.comp_app] using
    congrArg (fun f => f.app a) (ed.s_comp_δ n i)

/-- Evaluated last extra degeneracies commute with degeneracies. -/
theorem s_comp_σ (n : ℕ) (i : Fin (n + 1)) :
    (ed.s n).app a ≫
        (SimplicialObject.Augmented.Pointwise.obj X a).left.σ i.castSucc =
      (SimplicialObject.Augmented.Pointwise.obj X a).left.σ i ≫
        (ed.s (n + 1)).app a := by
  change (ed.s n).app a ≫ (X.left.σ i.castSucc).app a =
    (X.left.σ i).app a ≫ (ed.s (n + 1)).app a
  simpa only [NatTrans.comp_app] using
    congrArg (fun f => f.app a) (ed.s_comp_σ n i)

end app

/-- Evaluate a last extra degeneracy on a functor-valued augmented simplicial object at one
object. -/
@[stacks 08ND "objectwise evaluation of a last extra degeneracy"]
def app {A : Type u'} [Category.{v'} A]
    {X : SimplicialObject.Augmented (A ⥤ C)}
    (ed : LastExtraDegeneracy X) (a : A) :
    LastExtraDegeneracy (SimplicialObject.Augmented.Pointwise.obj X a) where
  s' := ed.s'.app a
  s n := (ed.s n).app a
  s'_comp_ε := app.s'_comp_ε ed a
  s₀_comp_δ₀ := app.s₀_comp_δ₀ ed a
  s_comp_δ_last := app.s_comp_δ_last ed a
  s_comp_δ := app.s_comp_δ ed a
  s_comp_σ := app.s_comp_σ ed a

/-- The zero-section of an evaluated last extra degeneracy is evaluated pointwise. -/
@[simp]
theorem app_s' {A : Type u'} [Category.{v'} A]
    {X : SimplicialObject.Augmented (A ⥤ C)}
    (ed : LastExtraDegeneracy X) (a : A) :
    (ed.app a).s' = ed.s'.app a := rfl

/-- Each map of an evaluated last extra degeneracy is evaluated pointwise. -/
@[simp]
theorem app_s {A : Type u'} [Category.{v'} A]
    {X : SimplicialObject.Augmented (A ⥤ C)}
    (ed : LastExtraDegeneracy X) (a : A) (n : ℕ) :
    (ed.app a).s n = (ed.s n).app a := rfl

namespace ofIso

variable {Y : SimplicialObject.Augmented C} (e : X ≅ Y)

/-- The transported degree-zero section is a section of the target augmentation. -/
theorem s'_comp_ε :
    ((SimplicialObject.Augmented.point.mapIso e).inv ≫ ed.s' ≫
        (SimplicialObject.Augmented.drop.mapIso e).hom.app (op ⦋0⦌)) ≫
      Y.hom.app (op ⦋0⦌) = 𝟙 Y.right := by
  set_option backward.isDefEq.respectTransparency false in
    change (e.inv.right ≫ ed.s' ≫ e.hom.left.app (op ⦋0⦌)) ≫
      Y.hom.app (op ⦋0⦌) = 𝟙 Y.right
    rw [Category.assoc, Category.assoc, w_app e.hom, ed.s'_comp_ε_assoc, Category.id_comp]
    exact (SimplicialObject.Augmented.point.mapIso e).inv_hom_id

/-- The transported initial last-degeneracy relation. -/
theorem s₀_comp_δ₀ :
    ((SimplicialObject.Augmented.drop.mapIso e).inv.app (op ⦋0⦌) ≫ ed.s 0 ≫
        (SimplicialObject.Augmented.drop.mapIso e).hom.app (op ⦋1⦌)) ≫
      Y.left.δ 0 =
        Y.hom.app (op ⦋0⦌) ≫
          ((SimplicialObject.Augmented.point.mapIso e).inv ≫ ed.s' ≫
            (SimplicialObject.Augmented.drop.mapIso e).hom.app (op ⦋0⦌)) := by
  set_option backward.isDefEq.respectTransparency false in
    change (e.inv.left.app (op ⦋0⦌) ≫ ed.s 0 ≫ e.hom.left.app (op ⦋1⦌)) ≫
      Y.left.δ 0 = Y.hom.app (op ⦋0⦌) ≫
        e.inv.right ≫ ed.s' ≫ e.hom.left.app (op ⦋0⦌)
    rw [Category.assoc, Category.assoc,
      ← SimplicialObject.δ_naturality e.hom.left 0, ed.s₀_comp_δ₀_assoc]
    simpa only [Category.assoc] using
      congrArg (fun f => f ≫ ed.s' ≫ e.hom.left.app (op ⦋0⦌)) (w_app e.inv (op ⦋0⦌))

/-- Transported last extra degeneracies remain sections of the final faces. -/
theorem s_comp_δ_last (n : ℕ) :
    ((SimplicialObject.Augmented.drop.mapIso e).inv.app (op ⦋n⦌) ≫ ed.s n ≫
        (SimplicialObject.Augmented.drop.mapIso e).hom.app (op ⦋n + 1⦌)) ≫
      Y.left.δ (Fin.last (n + 1)) = 𝟙 _ := by
  change (e.inv.left.app (op ⦋n⦌) ≫ ed.s n ≫
    e.hom.left.app (op ⦋n + 1⦌)) ≫ Y.left.δ (Fin.last (n + 1)) = 𝟙 _
  rw [Category.assoc, Category.assoc, ← SimplicialObject.δ_naturality,
    ed.s_comp_δ_last_assoc]
  exact congr_app (SimplicialObject.Augmented.drop.mapIso e).inv_hom_id (op ⦋n⦌)

/-- Transported last extra degeneracies commute with nonfinal faces. -/
theorem s_comp_δ (n : ℕ) (i : Fin (n + 2)) :
    ((SimplicialObject.Augmented.drop.mapIso e).inv.app (op ⦋n + 1⦌) ≫
        ed.s (n + 1) ≫
          (SimplicialObject.Augmented.drop.mapIso e).hom.app (op ⦋n + 2⦌)) ≫
      Y.left.δ i.castSucc =
        Y.left.δ i ≫
          ((SimplicialObject.Augmented.drop.mapIso e).inv.app (op ⦋n⦌) ≫ ed.s n ≫
            (SimplicialObject.Augmented.drop.mapIso e).hom.app (op ⦋n + 1⦌)) := by
  set_option backward.isDefEq.respectTransparency false in
    change (e.inv.left.app (op ⦋n + 1⦌) ≫ ed.s (n + 1) ≫
      e.hom.left.app (op ⦋n + 2⦌)) ≫ Y.left.δ i.castSucc =
        Y.left.δ i ≫ e.inv.left.app (op ⦋n⦌) ≫ ed.s n ≫ e.hom.left.app (op ⦋n + 1⦌)
    rw [Category.assoc, Category.assoc,
      ← SimplicialObject.δ_naturality e.hom.left i.castSucc, ed.s_comp_δ_assoc]
    simpa only [Category.assoc] using
      congrArg (fun f => f ≫ ed.s n ≫ e.hom.left.app (op ⦋n + 1⦌))
        (SimplicialObject.δ_naturality e.inv.left i).symm

/-- Transported last extra degeneracies commute with degeneracies. -/
theorem s_comp_σ (n : ℕ) (i : Fin (n + 1)) :
    ((SimplicialObject.Augmented.drop.mapIso e).inv.app (op ⦋n⦌) ≫ ed.s n ≫
        (SimplicialObject.Augmented.drop.mapIso e).hom.app (op ⦋n + 1⦌)) ≫
      Y.left.σ i.castSucc =
        Y.left.σ i ≫
          ((SimplicialObject.Augmented.drop.mapIso e).inv.app (op ⦋n + 1⦌) ≫
            ed.s (n + 1) ≫
              (SimplicialObject.Augmented.drop.mapIso e).hom.app (op ⦋n + 2⦌)) := by
  set_option backward.isDefEq.respectTransparency false in
    change (e.inv.left.app (op ⦋n⦌) ≫ ed.s n ≫
      e.hom.left.app (op ⦋n + 1⦌)) ≫ Y.left.σ i.castSucc =
        Y.left.σ i ≫ e.inv.left.app (op ⦋n + 1⦌) ≫ ed.s (n + 1) ≫
          e.hom.left.app (op ⦋n + 2⦌)
    rw [Category.assoc, Category.assoc,
      ← SimplicialObject.σ_naturality e.hom.left i.castSucc, ed.s_comp_σ_assoc]
    simpa only [Category.assoc] using
      congrArg (fun f => f ≫ ed.s (n + 1) ≫ e.hom.left.app (op ⦋n + 2⦌))
        (SimplicialObject.σ_naturality e.inv.left i).symm

end ofIso

/-- Transport a last extra degeneracy across an isomorphism of augmented simplicial objects. -/
@[stacks 08ND "isomorphism invariance of last extra degeneracies"]
def ofIso {Y : SimplicialObject.Augmented C} (e : X ≅ Y) (ed : LastExtraDegeneracy X) :
    LastExtraDegeneracy Y where
  s' := (SimplicialObject.Augmented.point.mapIso e).inv ≫ ed.s' ≫
    (SimplicialObject.Augmented.drop.mapIso e).hom.app (op ⦋0⦌)
  s n := (SimplicialObject.Augmented.drop.mapIso e).inv.app (op ⦋n⦌) ≫ ed.s n ≫
    (SimplicialObject.Augmented.drop.mapIso e).hom.app (op ⦋n + 1⦌)
  s'_comp_ε := ofIso.s'_comp_ε ed e
  s₀_comp_δ₀ := ofIso.s₀_comp_δ₀ ed e
  s_comp_δ_last := ofIso.s_comp_δ_last ed e
  s_comp_δ := ofIso.s_comp_δ ed e
  s_comp_σ := ofIso.s_comp_σ ed e

/-- The degree-zero section of a transported last extra degeneracy is the conjugated source
section. -/
@[simp, stacks 08ND "transported last extra degeneracy zero-section"]
theorem ofIso_s' {Y : SimplicialObject.Augmented C} (e : X ≅ Y) (ed : LastExtraDegeneracy X) :
    (ofIso e ed).s' =
      (SimplicialObject.Augmented.point.mapIso e).inv ≫ ed.s' ≫
        (SimplicialObject.Augmented.drop.mapIso e).hom.app (op ⦋0⦌) := rfl

/-- The degreewise maps of a transported last extra degeneracy are the conjugated source maps. -/
@[simp, stacks 08ND "transported last extra degeneracy maps"]
theorem ofIso_s {Y : SimplicialObject.Augmented C} (e : X ≅ Y) (ed : LastExtraDegeneracy X)
    (n : ℕ) :
    (ofIso e ed).s n =
      (SimplicialObject.Augmented.drop.mapIso e).inv.app (op ⦋n⦌) ≫ ed.s n ≫
        (SimplicialObject.Augmented.drop.mapIso e).hom.app (op ⦋n + 1⦌) := rfl

/-- The simplicial section of the augmentation generated by the degree-zero section of a last
extra degeneracy. -/
@[stacks 08ND "simplicial section from a last extra degeneracy"]
def section_ : (SimplicialObject.const C).obj X.right ⟶ X.left :=
  X.left.fromZero ed.s'

/-- Every component of the section supplied by a last extra degeneracy is generated from its
degree-zero component. -/
@[simp, stacks 08ND "component of the section from a last extra degeneracy"]
theorem section_app (Δ : SimplexCategoryᵒᵖ) :
    ed.section_.app Δ =
      ed.s' ≫ X.left.map (SimplexCategory.isTerminalZero.from (unop Δ)).op := rfl

/-- In degree zero, the simplicial section supplied by a last extra degeneracy is its defining
section. -/
@[simp, stacks 08ND "degree-zero section from a last extra degeneracy"]
theorem section_app_zero : ed.section_.app (op ⦋0⦌) = ed.s' := by
  rw [section_app, Limits.IsTerminal.from_self, op_id, Functor.map_id, Category.comp_id]

/-- Iterating the final degeneracy from the degree-zero section gives every component of the
canonical simplicial section. -/
@[reassoc (attr := simp), stacks 08ND "last-extra-degeneracy section in every degree"]
theorem s'_σLastIter (n : ℕ) :
    ed.s' ≫ X.left.σLastIter n (zero_add n) = ed.section_.app (op ⦋n⦌) := by
  rw [section_app]
  dsimp [SimplicialObject.σLastIter]
  congr 3
  subsingleton

/-- The simplicial section supplied by a last extra degeneracy is a strict section of the
augmentation. -/
@[simp, stacks 08ND "section identity from a last extra degeneracy"]
theorem section_comp_hom : ed.section_ ≫ X.hom = 𝟙 _ := by
  set_option backward.isDefEq.respectTransparency false in
    apply NatTrans.ext
    funext Δ
    change ed.section_.app Δ ≫ X.hom.app Δ = 𝟙 X.right
    have h : X.left.map (SimplexCategory.isTerminalZero.from (unop Δ)).op ≫ X.hom.app Δ =
        X.hom.app (op ⦋0⦌) :=
      (X.hom.naturality (SimplexCategory.isTerminalZero.from (unop Δ)).op).trans
        (Category.comp_id _)
    rw [section_app, Category.assoc, h]
    exact ed.s'_comp_ε

/-- A last extra degeneracy canonically exhibits its augmentation as a split epimorphism. -/
@[stacks 08ND "split epimorphism from a last extra degeneracy"]
def splitEpi : SplitEpi X.hom where
  section_ := ed.section_
  id := ed.section_comp_hom

end LastExtraDegeneracy

end CategoryTheory.SimplicialObject.Augmented
