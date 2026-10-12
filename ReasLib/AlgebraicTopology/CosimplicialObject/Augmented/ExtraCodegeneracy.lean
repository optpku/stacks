/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Augmented.Composition.Pointwise
public import ReasLib.CategoryTheory.Functor.Const.Adjunction

/-!
# Extra codegeneracies on augmented cosimplicial objects

An extra codegeneracy contracts the zeroth coface of an augmented cosimplicial object. This leaf
owns the generic structure, its transport API, and its canonical retraction. Homotopical
consequences live in the separate `ExtraCodegeneracy/Homotopy` leaf.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped Simplicial

universe u v u' v'

namespace CategoryTheory.CosimplicialObject.Augmented

variable {C : Type u} [Category.{v} C]

/-- An extra codegeneracy on an augmented cosimplicial object. Its distinguished codegeneracy
retracts the zeroth coface; the remaining relations use successor indices. -/
@[ext, stacks 0FKS "extra codegeneracy on an augmented cosimplicial object"]
structure ExtraCodegeneracy (X : CosimplicialObject.Augmented C) where
  /-- A retraction of the coaugmentation in degree zero. -/
  s' : X.right ^⦋0⦌ ⟶ X.left
  /-- The extra codegeneracy in every cosimplicial degree. -/
  s : ∀ n : ℕ, X.right ^⦋n + 1⦌ ⟶ X.right ^⦋n⦌
  /-- The degree-zero retraction splits the coaugmentation. -/
  η_comp_s' : X.hom.app ⦋0⦌ ≫ s' = 𝟙 X.left
  /-- The first coface followed by the first extra codegeneracy factors through the
  coaugmentation and its retraction. -/
  δ₁_comp_s₀ : X.right.δ 1 ≫ s 0 = s' ≫ X.hom.app ⦋0⦌
  /-- Every extra codegeneracy retracts the zeroth coface. -/
  δ₀_comp_s : ∀ n : ℕ, X.right.δ 0 ≫ s n = 𝟙 _
  /-- Positive cofaces commute with the extra codegeneracies. -/
  δ_comp_s : ∀ (n : ℕ) (i : Fin (n + 2)),
    X.right.δ i.succ ≫ s (n + 1) = s n ≫ X.right.δ i
  /-- Positive codegeneracies commute with the extra codegeneracies. -/
  σ_comp_s : ∀ (n : ℕ) (i : Fin (n + 1)),
    X.right.σ i.succ ≫ s n = s (n + 1) ≫ X.right.σ i

namespace ExtraCodegeneracy

variable {X : CosimplicialObject.Augmented C} (ed : ExtraCodegeneracy X)

attribute [reassoc] δ₁_comp_s₀ δ_comp_s σ_comp_s
attribute [reassoc (attr := simp)] η_comp_s' δ₀_comp_s

namespace map

variable {D : Type u'} [Category.{v'} D] (F : C ⥤ D)

/-- The mapped degree-zero retraction splits the mapped coaugmentation. -/
@[stacks 0FKS "mapped degree-zero extra-codegeneracy retraction"]
theorem η_comp_s' :
    (((CosimplicialObject.Augmented.whiskering C D).obj F).obj X).hom.app ⦋0⦌ ≫
        F.map ed.s' =
      𝟙 (F.obj X.left) := sorry

/-- The mapped initial extra-codegeneracy relation. -/
@[stacks 0FKS "mapped initial extra-codegeneracy relation"]
theorem δ₁_comp_s₀ :
    (((CosimplicialObject.Augmented.whiskering C D).obj F).obj X).right.δ 1 ≫
        F.map (ed.s 0) =
      F.map ed.s' ≫
        (((CosimplicialObject.Augmented.whiskering C D).obj F).obj X).hom.app ⦋0⦌ := sorry

/-- Mapped extra codegeneracies still retract the zeroth cofaces. -/
@[stacks 0FKS "mapped zeroth-coface extra-codegeneracy relation"]
theorem δ₀_comp_s (n : ℕ) :
    (((CosimplicialObject.Augmented.whiskering C D).obj F).obj X).right.δ 0 ≫
        F.map (ed.s n) =
      𝟙 _ := sorry

/-- Mapped extra codegeneracies commute with positive cofaces. -/
@[stacks 0FKS "mapped coface extra-codegeneracy relation"]
theorem δ_comp_s (n : ℕ) (i : Fin (n + 2)) :
    (((CosimplicialObject.Augmented.whiskering C D).obj F).obj X).right.δ i.succ ≫
        F.map (ed.s (n + 1)) =
      F.map (ed.s n) ≫
        (((CosimplicialObject.Augmented.whiskering C D).obj F).obj X).right.δ i := sorry

/-- Mapped extra codegeneracies commute with positive codegeneracies. -/
@[stacks 0FKS "mapped codegeneracy extra-codegeneracy relation"]
theorem σ_comp_s (n : ℕ) (i : Fin (n + 1)) :
    (((CosimplicialObject.Augmented.whiskering C D).obj F).obj X).right.σ i.succ ≫
        F.map (ed.s n) =
      F.map (ed.s (n + 1)) ≫
        (((CosimplicialObject.Augmented.whiskering C D).obj F).obj X).right.σ i := sorry

end map

/-- Extra codegeneracies are preserved by applying a functor to an augmented cosimplicial
object. -/
@[stacks 0FKS "functoriality of extra codegeneracies"]
def map {D : Type u'} [Category.{v'} D] (F : C ⥤ D) :
    ExtraCodegeneracy
      (((CosimplicialObject.Augmented.whiskering C D).obj F).obj X) where
  s' := F.map ed.s'
  s n := F.map (ed.s n)
  η_comp_s' := map.η_comp_s' ed F
  δ₁_comp_s₀ := map.δ₁_comp_s₀ ed F
  δ₀_comp_s := map.δ₀_comp_s ed F
  δ_comp_s := map.δ_comp_s ed F
  σ_comp_s := map.σ_comp_s ed F

/-- The degree-zero retraction of a mapped extra codegeneracy is obtained by applying the
functor. -/
@[simp, stacks 0FKS "mapped extra codegeneracy zero-retraction"]
theorem map_s' {D : Type u'} [Category.{v'} D] (F : C ⥤ D) :
    (ed.map F).s' = F.map ed.s' := sorry

/-- The degreewise maps of a mapped extra codegeneracy are obtained by applying the functor. -/
@[simp, stacks 0FKS "mapped extra codegeneracy maps"]
theorem map_s {D : Type u'} [Category.{v'} D] (F : C ⥤ D) (n : ℕ) :
    (ed.map F).s n = F.map (ed.s n) := sorry

namespace app

variable {A : Type u'} [Category.{v'} A]
variable {X : CosimplicialObject.Augmented (A ⥤ C)}
variable (ed : ExtraCodegeneracy X) (a : A)

/-- The evaluated degree-zero retraction splits the evaluated coaugmentation. -/
@[stacks 0FKS "evaluated degree-zero extra-codegeneracy retraction"]
theorem η_comp_s' :
    (CosimplicialObject.Augmented.Pointwise.obj X a).hom.app ⦋0⦌ ≫ ed.s'.app a =
      𝟙 ((CosimplicialObject.Augmented.Pointwise.obj X a).left) := sorry

/-- The initial extra-codegeneracy relation holds after evaluation. -/
@[stacks 0FKS "evaluated initial extra-codegeneracy relation"]
theorem δ₁_comp_s₀ :
    (CosimplicialObject.Augmented.Pointwise.obj X a).right.δ 1 ≫ (ed.s 0).app a =
      ed.s'.app a ≫ (CosimplicialObject.Augmented.Pointwise.obj X a).hom.app ⦋0⦌ := sorry

/-- Evaluated extra codegeneracies still retract the zeroth cofaces. -/
@[stacks 0FKS "evaluated zeroth-coface extra-codegeneracy relation"]
theorem δ₀_comp_s (n : ℕ) :
    (CosimplicialObject.Augmented.Pointwise.obj X a).right.δ 0 ≫ (ed.s n).app a =
      𝟙 _ := sorry

/-- Evaluated extra codegeneracies commute with positive cofaces. -/
@[stacks 0FKS "evaluated coface extra-codegeneracy relation"]
theorem δ_comp_s (n : ℕ) (i : Fin (n + 2)) :
    (CosimplicialObject.Augmented.Pointwise.obj X a).right.δ i.succ ≫
        (ed.s (n + 1)).app a =
      (ed.s n).app a ≫
        (CosimplicialObject.Augmented.Pointwise.obj X a).right.δ i := sorry

/-- Evaluated extra codegeneracies commute with positive codegeneracies. -/
@[stacks 0FKS "evaluated codegeneracy extra-codegeneracy relation"]
theorem σ_comp_s (n : ℕ) (i : Fin (n + 1)) :
    (CosimplicialObject.Augmented.Pointwise.obj X a).right.σ i.succ ≫ (ed.s n).app a =
      (ed.s (n + 1)).app a ≫
        (CosimplicialObject.Augmented.Pointwise.obj X a).right.σ i := sorry

end app

/-- Evaluate an extra codegeneracy on a functor-valued augmented cosimplicial object at one
object. -/
@[stacks 0FKS "objectwise evaluation of an extra codegeneracy"]
def app {A : Type u'} [Category.{v'} A]
    {X : CosimplicialObject.Augmented (A ⥤ C)}
    (ed : ExtraCodegeneracy X) (a : A) :
    ExtraCodegeneracy (CosimplicialObject.Augmented.Pointwise.obj X a) where
  s' := ed.s'.app a
  s n := (ed.s n).app a
  η_comp_s' := app.η_comp_s' ed a
  δ₁_comp_s₀ := app.δ₁_comp_s₀ ed a
  δ₀_comp_s := app.δ₀_comp_s ed a
  δ_comp_s := app.δ_comp_s ed a
  σ_comp_s := app.σ_comp_s ed a

/-- The degree-zero retraction of an evaluated extra codegeneracy is evaluated pointwise. -/
@[simp, stacks 0FKS "evaluated extra codegeneracy zero-retraction"]
theorem app_s' {A : Type u'} [Category.{v'} A]
    {X : CosimplicialObject.Augmented (A ⥤ C)}
    (ed : ExtraCodegeneracy X) (a : A) :
    (ed.app a).s' = ed.s'.app a := sorry

/-- Each map of an evaluated extra codegeneracy is evaluated pointwise. -/
@[simp, stacks 0FKS "evaluated extra codegeneracy maps"]
theorem app_s {A : Type u'} [Category.{v'} A]
    {X : CosimplicialObject.Augmented (A ⥤ C)}
    (ed : ExtraCodegeneracy X) (a : A) (n : ℕ) :
    (ed.app a).s n = (ed.s n).app a := sorry

namespace ofIso

variable {Y : CosimplicialObject.Augmented C} (e : X ≅ Y)

/-- The transported degree-zero retraction splits the target coaugmentation. -/
@[stacks 0FKS "transported degree-zero extra-codegeneracy retraction"]
theorem η_comp_s' :
    Y.hom.app ⦋0⦌ ≫
        ((CosimplicialObject.Augmented.drop.mapIso e).inv.app ⦋0⦌ ≫ ed.s' ≫
          (CosimplicialObject.Augmented.point.mapIso e).hom) =
      𝟙 Y.left := sorry

/-- The initial extra-codegeneracy relation is preserved by transport. -/
@[stacks 0FKS "transported initial extra-codegeneracy relation"]
theorem δ₁_comp_s₀ :
    Y.right.δ 1 ≫
        ((CosimplicialObject.Augmented.drop.mapIso e).inv.app ⦋1⦌ ≫ ed.s 0 ≫
          (CosimplicialObject.Augmented.drop.mapIso e).hom.app ⦋0⦌) =
      ((CosimplicialObject.Augmented.drop.mapIso e).inv.app ⦋0⦌ ≫ ed.s' ≫
          (CosimplicialObject.Augmented.point.mapIso e).hom) ≫
        Y.hom.app ⦋0⦌ := sorry

/-- Transported extra codegeneracies still retract the zeroth cofaces. -/
@[stacks 0FKS "transported zeroth-coface extra-codegeneracy relation"]
theorem δ₀_comp_s (n : ℕ) :
    Y.right.δ 0 ≫
        ((CosimplicialObject.Augmented.drop.mapIso e).inv.app ⦋n + 1⦌ ≫ ed.s n ≫
          (CosimplicialObject.Augmented.drop.mapIso e).hom.app ⦋n⦌) =
      𝟙 _ := sorry

/-- Transported extra codegeneracies commute with positive cofaces. -/
@[stacks 0FKS "transported coface extra-codegeneracy relation"]
theorem δ_comp_s (n : ℕ) (i : Fin (n + 2)) :
    Y.right.δ i.succ ≫
        ((CosimplicialObject.Augmented.drop.mapIso e).inv.app ⦋n + 2⦌ ≫
          ed.s (n + 1) ≫
            (CosimplicialObject.Augmented.drop.mapIso e).hom.app ⦋n + 1⦌) =
      ((CosimplicialObject.Augmented.drop.mapIso e).inv.app ⦋n + 1⦌ ≫ ed.s n ≫
          (CosimplicialObject.Augmented.drop.mapIso e).hom.app ⦋n⦌) ≫
        Y.right.δ i := sorry

/-- Transported extra codegeneracies commute with positive codegeneracies. -/
@[stacks 0FKS "transported codegeneracy extra-codegeneracy relation"]
theorem σ_comp_s (n : ℕ) (i : Fin (n + 1)) :
    Y.right.σ i.succ ≫
        ((CosimplicialObject.Augmented.drop.mapIso e).inv.app ⦋n + 1⦌ ≫ ed.s n ≫
          (CosimplicialObject.Augmented.drop.mapIso e).hom.app ⦋n⦌) =
      ((CosimplicialObject.Augmented.drop.mapIso e).inv.app ⦋n + 2⦌ ≫
          ed.s (n + 1) ≫
            (CosimplicialObject.Augmented.drop.mapIso e).hom.app ⦋n + 1⦌) ≫
        Y.right.σ i := sorry

end ofIso

/-- Transport an extra codegeneracy across an isomorphism of augmented cosimplicial objects. -/
@[stacks 0FKS "isomorphism invariance of extra codegeneracies"]
def ofIso {Y : CosimplicialObject.Augmented C} (e : X ≅ Y)
    (ed : ExtraCodegeneracy X) : ExtraCodegeneracy Y where
  s' := (CosimplicialObject.Augmented.drop.mapIso e).inv.app ⦋0⦌ ≫ ed.s' ≫
    (CosimplicialObject.Augmented.point.mapIso e).hom
  s n := (CosimplicialObject.Augmented.drop.mapIso e).inv.app ⦋n + 1⦌ ≫ ed.s n ≫
    (CosimplicialObject.Augmented.drop.mapIso e).hom.app ⦋n⦌
  η_comp_s' := ofIso.η_comp_s' ed e
  δ₁_comp_s₀ := ofIso.δ₁_comp_s₀ ed e
  δ₀_comp_s := ofIso.δ₀_comp_s ed e
  δ_comp_s := ofIso.δ_comp_s ed e
  σ_comp_s := ofIso.σ_comp_s ed e

/-- The degree-zero retraction of a transported extra codegeneracy is conjugated by the point
and cosimplicial isomorphisms. -/
@[simp, stacks 0FKS "transported extra codegeneracy zero-retraction"]
theorem ofIso_s' {Y : CosimplicialObject.Augmented C} (e : X ≅ Y)
    (ed : ExtraCodegeneracy X) :
    (ofIso e ed).s' =
      (CosimplicialObject.Augmented.drop.mapIso e).inv.app ⦋0⦌ ≫ ed.s' ≫
        (CosimplicialObject.Augmented.point.mapIso e).hom := sorry

/-- The degreewise maps of a transported extra codegeneracy are conjugated by the
cosimplicial isomorphism. -/
@[simp, stacks 0FKS "transported extra codegeneracy maps"]
theorem ofIso_s {Y : CosimplicialObject.Augmented C} (e : X ≅ Y)
    (ed : ExtraCodegeneracy X) (n : ℕ) :
    (ofIso e ed).s n =
      (CosimplicialObject.Augmented.drop.mapIso e).inv.app ⦋n + 1⦌ ≫ ed.s n ≫
        (CosimplicialObject.Augmented.drop.mapIso e).hom.app ⦋n⦌ := sorry

/-- Transport along the identity isomorphism preserves an extra codegeneracy. -/
@[simp, stacks 0FKS "identity transport of an extra codegeneracy"]
theorem ofIso_refl : ofIso (Iso.refl X) ed = ed := sorry

/-- Transporting an extra codegeneracy across two isomorphisms agrees with transport across
their composite. -/
@[stacks 0FKS "composition of extra codegeneracy transports"]
theorem ofIso_trans {Y Z : CosimplicialObject.Augmented C}
    (e : X ≅ Y) (f : Y ≅ Z) :
    ofIso (e ≪≫ f) ed = ofIso f (ofIso e ed) := sorry

/-- The cosimplicial retraction generated by the degree-zero retraction of an extra
codegeneracy. -/
@[stacks 0FKS "cosimplicial retraction from an extra codegeneracy"]
def retraction : X.right ⟶ (CosimplicialObject.const C).obj X.left :=
  SimplexCategory.isTerminalZero.toConst ed.s'

/-- Every component of the retraction is the unique map to degree zero followed by the chosen
degree-zero retraction. -/
@[simp, stacks 0FKS "component of the extra-codegeneracy retraction"]
theorem retraction.app (Δ : SimplexCategory) :
    ed.retraction.app Δ =
      X.right.map (SimplexCategory.isTerminalZero.from Δ) ≫ ed.s' := sorry

/-- The degree-zero component of the cosimplicial retraction is its defining retraction. -/
@[simp, stacks 0FKS "degree-zero extra-codegeneracy retraction"]
theorem retraction.app_zero : ed.retraction.app ⦋0⦌ = ed.s' := sorry

/-- Applying a functor to an extra codegeneracy commutes with forming the canonical
retraction. -/
@[stacks 0FKS "functoriality of the extra-codegeneracy retraction"]
theorem map_retraction {D : Type u'} [Category.{v'} D] (F : C ⥤ D) :
    (ed.map F).retraction =
      Functor.whiskerRight ed.retraction F ≫
        (Functor.constComp SimplexCategory X.left F).hom := sorry

/-- Componentwise, the canonical retraction of a mapped extra codegeneracy is obtained by
applying the functor. -/
@[simp, stacks 0FKS "component of a mapped extra-codegeneracy retraction"]
theorem map_retraction_app {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    (Δ : SimplexCategory) :
    (ed.map F).retraction.app Δ = F.map (ed.retraction.app Δ) := sorry

/-- Evaluating a functor-valued extra codegeneracy commutes with forming the canonical
retraction. -/
@[stacks 0FKS "pointwise evaluation of the extra-codegeneracy retraction"]
theorem app_retraction {A : Type u'} [Category.{v'} A]
    {X : CosimplicialObject.Augmented (A ⥤ C)}
    (ed : ExtraCodegeneracy X) (a : A) :
    (ed.app a).retraction = NatTrans.flipApp ed.retraction a := sorry

/-- Components of the canonical retraction evaluate pointwise. -/
@[simp, stacks 0FKS "component of an evaluated extra-codegeneracy retraction"]
theorem app_retraction_app {A : Type u'} [Category.{v'} A]
    {X : CosimplicialObject.Augmented (A ⥤ C)}
    (ed : ExtraCodegeneracy X) (a : A) (Δ : SimplexCategory) :
    (ed.app a).retraction.app Δ = (ed.retraction.app Δ).app a := sorry

/-- Transporting an extra codegeneracy across an isomorphism conjugates its canonical
retraction by the induced point and cosimplicial isomorphisms. -/
@[stacks 0FKS "transported extra-codegeneracy retraction"]
theorem ofIso_retraction {Y : CosimplicialObject.Augmented C} (e : X ≅ Y) :
    (ofIso e ed).retraction =
      (CosimplicialObject.Augmented.drop.mapIso e).inv ≫ ed.retraction ≫
        (CosimplicialObject.const C).map
          (CosimplicialObject.Augmented.point.mapIso e).hom := sorry

/-- The coaugmentation followed by the retraction supplied by an extra codegeneracy is the
identity of the constant cosimplicial object. -/
@[simp, stacks 0FKS "coaugmentation-retraction identity from an extra codegeneracy"]
theorem hom_comp_retraction :
    X.hom ≫ ed.retraction = 𝟙 ((CosimplicialObject.const C).obj X.left) := sorry

/-- An extra codegeneracy canonically exhibits its coaugmentation as a split monomorphism. -/
@[stacks 0FKS "split monomorphism from an extra codegeneracy"]
def splitMono : SplitMono X.hom where
  retraction := ed.retraction
  id := ed.hom_comp_retraction

end ExtraCodegeneracy

end CategoryTheory.CosimplicialObject.Augmented
