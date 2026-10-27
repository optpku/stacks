/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Reindex.Lift
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Definition
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.CategoryTheory.Category.Cat

/-!
# Quotienting arrows by local equality

The separated category has the same objects as the original category.
Arrows are quotient classes of original arrows, and
Cartesian factorization descends the original input factor through the quotient.
-/

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory

noncomputable section

universe u v uX vX

namespace CategoryTheory.Functor.StackificationConstruction

variable {C : Type u} [Category.{v} C] {X : Type uX} [Category.{vX} X]
variable (J : GrothendieckTopology C) (p : X ⥤ C) (χ : p.Cleavage)

private theorem equalitySieve_laws {a b : X} (f g : a ⟶ b) :
    ∀ {V W : C} (k : V ⟶ p.obj a),
      χ.cartesianHom k (⟨a, rfl⟩ : p.Fiber (p.obj a)) ≫ f =
        χ.cartesianHom k (⟨a, rfl⟩ : p.Fiber (p.obj a)) ≫ g →
      ∀ l : W ⟶ V,
        χ.cartesianHom (l ≫ k) (⟨a, rfl⟩ : p.Fiber (p.obj a)) ≫ f =
          χ.cartesianHom (l ≫ k) (⟨a, rfl⟩ : p.Fiber (p.obj a)) ≫ g := by
  intro V W k h l
  let first := χ.reindexLift k (⟨a, rfl⟩ : p.Fiber (p.obj a))
  let second := χ.reindexLift (l ≫ k) (⟨a, rfl⟩ : p.Fiber (p.obj a))
  letI := first.isStronglyCartesian
  letI := second.isStronglyCartesian
  let q := Functor.IsStronglyCartesian.map p k first.hom (g := l) rfl second.hom
  have hq : q ≫ first.hom = second.hom := Functor.IsStronglyCartesian.fac p k first.hom _ _
  change first.hom ≫ f = first.hom ≫ g at h
  change second.hom ≫ f = second.hom ≫ g
  calc
    second.hom ≫ f = (q ≫ first.hom) ≫ f := by rw [hq]
    _ = (q ≫ first.hom) ≫ g := by
      simpa only [Category.assoc] using congrArg (fun t ↦ q ≫ t) h
    _ = second.hom ≫ g := by rw [hq]

/-- Arrows on which two original total arrows become equal after the displayed
Cartesian restriction of their common source. -/
def equalitySieve {a b : X} (f g : a ⟶ b) : Sieve (p.obj a) where
  arrows _ k := χ.cartesianHom k (⟨a, rfl⟩ : p.Fiber (p.obj a)) ≫ f =
    χ.cartesianHom k (⟨a, rfl⟩ : p.Fiber (p.obj a)) ≫ g
  downward_closed := fun {_ _} {k} hk l ↦ equalitySieve_laws p χ f g k hk l

/-- The projected arrow is fixed, and equality holds on a covering sieve. -/
def LocallyEqual {a b : X} (f g : a ⟶ b) : Prop :=
  p.map f = p.map g ∧ equalitySieve p χ f g ∈ J (p.obj a)

private theorem locallyEqual_cancel_stronglyCartesian {a b c : X} {R S : C}
    (f : R ⟶ S) (φ : a ⟶ b) [p.IsStronglyCartesian f φ]
    (k : p.obj c ⟶ R) (α β : c ⟶ a) (hα : p.IsHomLift k α) (hβ : p.IsHomLift k β)
    (h : LocallyEqual J p χ (α ≫ φ) (β ≫ φ)) : LocallyEqual J p χ α β := by
  letI := hα
  letI := hβ
  refine ⟨(IsHomLift.fac' p k α).trans (IsHomLift.fac' p k β).symm,
    J.superset_covering ?_ h.2⟩
  intro V t ht
  let source := χ.reindexLift t (⟨c, rfl⟩ : p.Fiber (p.obj c))
  letI := source.isStronglyCartesian
  letI : p.IsHomLift (t ≫ k) (source.hom ≫ α) :=
    CategoryTheory.IsHomLift.comp p t k source.hom α
  letI : p.IsHomLift (t ≫ k) (source.hom ≫ β) :=
    CategoryTheory.IsHomLift.comp p t k source.hom β
  change source.hom ≫ α = source.hom ≫ β
  change source.hom ≫ (α ≫ φ) = source.hom ≫ (β ≫ φ) at ht
  apply Functor.IsStronglyCartesian.ext p f φ (t ≫ k)
  simpa only [Category.assoc] using ht

/-- Local equality is an equivalence relation on parallel arrows. -/
theorem locallyEqual_equivalence (a b : X) :
    _root_.Equivalence (@LocallyEqual _ _ _ _ J p χ a b) := by
  constructor
  · intro f
    refine ⟨rfl, J.covering_of_eq_top ?_⟩
    apply Sieve.ext
    intro V k
    exact ⟨fun _ ↦ trivial, fun _ ↦ rfl⟩
  · intro f g h
    refine ⟨h.1.symm, J.superset_covering ?_ h.2⟩
    intro V k hk
    exact hk.symm
  · intro f g h hfg hgh
    refine ⟨hfg.1.trans hgh.1, J.superset_covering ?_
      (J.intersection_covering hfg.2 hgh.2)⟩
    intro V k hk
    exact hk.1.trans hk.2

/-- Composition preserves local equality. -/
theorem locallyEqual_comp {a b c : X} {f f' : a ⟶ b} {g g' : b ⟶ c}
    (hf : LocallyEqual J p χ f f') (hg : LocallyEqual J p χ g g') :
    LocallyEqual J p χ (f ≫ g) (f' ≫ g') := by
  refine ⟨by simp only [Functor.map_comp, hf.1, hg.1], ?_⟩
  apply J.superset_covering (S := equalitySieve p χ f f' ⊓
    (equalitySieve p χ g g').pullback (p.map f')) ?_
    (J.intersection_covering hf.2 (J.pullback_stable (p.map f') hg.2))
  intro V k hk
  let source := χ.reindexLift k (⟨a, rfl⟩ : p.Fiber (p.obj a))
  let target := χ.reindexLift (k ≫ p.map f') (⟨b, rfl⟩ : p.Fiber (p.obj b))
  letI := source.isStronglyCartesian
  letI := target.isStronglyCartesian
  letI : p.IsHomLift (k ≫ p.map f') (source.hom ≫ f') :=
    CategoryTheory.IsHomLift.comp p k (p.map f') source.hom f'
  let q := Functor.IsCartesian.map p (k ≫ p.map f') target.hom (source.hom ≫ f')
  have hq : q ≫ target.hom = source.hom ≫ f' := Functor.IsCartesian.fac p _ _ _
  have hleft : source.hom ≫ f = source.hom ≫ f' := hk.1
  have hright : target.hom ≫ g = target.hom ≫ g' := hk.2
  change source.hom ≫ (f ≫ g) = source.hom ≫ (f' ≫ g')
  calc
    source.hom ≫ (f ≫ g) = (source.hom ≫ f') ≫ g := by
      rw [← Category.assoc, hleft]
    _ = (q ≫ target.hom) ≫ g := by rw [hq]
    _ = (q ≫ target.hom) ≫ g' := by
      simpa only [Category.assoc] using congrArg (fun t ↦ q ≫ t) hright
    _ = source.hom ≫ (f' ≫ g') := by rw [hq, Category.assoc]

/-- The setoid identifying arrows that agree locally over the same base arrow. -/
def localSetoid (a b : X) : Setoid (a ⟶ b) where
  r := LocallyEqual J p χ
  iseqv := locallyEqual_equivalence J p χ a b

/-- The separated stage retains each original object as explicit data. -/
structure SeparatedData (J : GrothendieckTopology C) (p : X ⥤ C) (χ : p.Cleavage) where
  /-- The underlying original object. -/
  obj : X

namespace SeparatedData

/-- Arrows are original arrows modulo local equality. -/
def Hom (a b : SeparatedData J p χ) := Quotient (localSetoid J p χ a.obj b.obj)

/-- The identity is the class of the original identity arrow. -/
def id (a : SeparatedData J p χ) : Hom J p χ a a := Quotient.mk'' (𝟙 a.obj)

/-- Composition is induced by composition of original representatives. -/
def comp {a b c : SeparatedData J p χ} (f : Hom J p χ a b) (g : Hom J p χ b c) :
    Hom J p χ a c :=
  Quotient.map₂ (fun f g ↦ f ≫ g) (fun _ _ h _ _ k ↦ locallyEqual_comp J p χ h k) f g

private theorem category_laws :
    (∀ (a b : SeparatedData J p χ) (f : Hom J p χ a b), comp J p χ (id J p χ a) f = f) ∧
    (∀ (a b : SeparatedData J p χ) (f : Hom J p χ a b), comp J p χ f (id J p χ b) = f) ∧
    (∀ (a b c d : SeparatedData J p χ) (f : Hom J p χ a b) (g : Hom J p χ b c)
      (h : Hom J p χ c d), comp J p χ (comp J p χ f g) h = comp J p χ f (comp J p χ g h)) := by
  constructor
  · intro a b f
    refine Quotient.inductionOn f ?_
    intro f
    change Quotient.mk'' (𝟙 a.obj ≫ f) = Quotient.mk'' f
    rw [Category.id_comp]
  · constructor
    · intro a b f
      refine Quotient.inductionOn f ?_
      intro f
      change Quotient.mk'' (f ≫ 𝟙 b.obj) = Quotient.mk'' f
      rw [Category.comp_id]
    · intro a b c d f g h
      refine Quotient.inductionOn f ?_
      intro f
      refine Quotient.inductionOn₂ g h ?_
      intro g h
      change Quotient.mk'' ((f ≫ g) ≫ h) = Quotient.mk'' (f ≫ (g ≫ h))
      rw [Category.assoc]

/-- The category on original objects with arrows modulo local equality. -/
@[reducible]
def category : Category.{vX} (SeparatedData J p χ) where
  Hom := Hom J p χ
  id := id J p χ
  comp := comp J p χ
  id_comp := fun f ↦ (category_laws J p χ).1 _ _ f
  comp_id := fun f ↦ (category_laws J p χ).2.1 _ _ f
  assoc := fun f g h ↦ (category_laws J p χ).2.2 _ _ _ _ f g h

end SeparatedData

/-- The bundled category of original objects and locally equal arrow classes. -/
def separatedCategory : Cat.{vX, uX} :=
  ⟨SeparatedData J p χ, SeparatedData.category J p χ⟩

/-- The carrier of the separated category. -/
abbrev Separated := (separatedCategory J p χ : Type uX)

namespace Separated

/-- The category supplied by the canonical separated bundle. -/
@[reducible]
def category : Category.{vX} (Separated J p χ) := Cat.str (separatedCategory J p χ)

private def projectionMap {a b : Separated J p χ} (f : a ⟶ b) : p.obj a.obj ⟶ p.obj b.obj :=
  Quotient.lift (fun (f : a.obj ⟶ b.obj) ↦ p.map f)
    (fun _ _ (h : LocallyEqual J p χ _ _) ↦ h.1) f

private theorem projection_laws :
    (∀ a : Separated J p χ, projectionMap J p χ (𝟙 a) = 𝟙 (p.obj a.obj)) ∧
    (∀ (a b c : Separated J p χ) (f : a ⟶ b) (g : b ⟶ c),
      projectionMap J p χ (f ≫ g) = projectionMap J p χ f ≫ projectionMap J p χ g) := by
  constructor
  · intro a
    exact p.map_id a.obj
  · intro a b c f g
    exact Quotient.inductionOn₂ f g (fun f g ↦ p.map_comp f g)

/-- The base arrow is evaluated on an original representative; local equality
contains exactly the equality required to make this well defined. -/
def projection : Separated J p χ ⥤ C where
  obj a := p.obj a.obj
  map := projectionMap J p χ
  map_id := (projection_laws J p χ).1
  map_comp := fun f g ↦ (projection_laws J p χ).2 _ _ _ f g

/-- The original functor sends an arrow to its literal local-equality class. -/
def ofOriginal : X ⥤ Separated J p χ where
  obj a := ⟨a⟩
  map f := Quotient.mk'' f
  map_id := fun _ ↦ rfl
  map_comp := fun _ _ ↦ rfl

/-- A representative of a quotient arrow has the same displayed lift condition. -/
theorem representative_isHomLift {a b : Separated J p χ} {R S : C} (f : R ⟶ S)
    (τ : a ⟶ b) [(projection J p χ).IsHomLift f τ] : p.IsHomLift f (Quotient.out τ) := by
  have he : p.map (Quotient.out τ) = (projection J p χ).map τ :=
    congrArg (projectionMap J p χ) (Quotient.out_eq τ)
  apply IsHomLift.of_fac p f (Quotient.out τ)
    (IsHomLift.domain_eq (projection J p χ) f τ)
    (IsHomLift.codomain_eq (projection J p χ) f τ)
  rw [he]
  exact IsHomLift.fac (projection J p χ) f τ

private theorem ofOriginal_isHomLift {a b : X} {R S : C} (f : R ⟶ S) (φ : a ⟶ b)
    (hφ : p.IsHomLift f φ) :
    (projection J p χ).IsHomLift f ((ofOriginal J p χ).map φ) := by
  cases hφ
  exact CategoryTheory.IsHomLift.map (projection J p χ) ((ofOriginal J p χ).map φ)

/-- Factor a quotient arrow through an original strongly Cartesian arrow,
using the original actual universal-property map on a quotient representative. -/
def factor {a b : X} {R S : C} (f : R ⟶ S) (φ : a ⟶ b)
    [p.IsStronglyCartesian f φ] {c : Separated J p χ} (k : p.obj c.obj ⟶ R)
    (τ : c ⟶ (ofOriginal J p χ).obj b) [(projection J p χ).IsHomLift (k ≫ f) τ] :
    c ⟶ (ofOriginal J p χ).obj a := by
  let raw : c.obj ⟶ b := Quotient.out τ
  exact Quotient.mk'' (@Functor.IsStronglyCartesian.map C X _ _ p R S a b f φ
    inferInstance (p.obj c.obj) c.obj k (k ≫ f) rfl raw
    (representative_isHomLift J p χ (k ≫ f) τ))

set_option backward.isDefEq.respectTransparency false in
private theorem mapIsStronglyCartesian_laws {a b : X} {R S : C} (f : R ⟶ S) (φ : a ⟶ b)
    [hφ : p.IsStronglyCartesian f φ] :
    (projection J p χ).IsHomLift f ((ofOriginal J p χ).map φ) ∧
    ∀ (c : Separated J p χ) (k : p.obj c.obj ⟶ R)
      (τ : c ⟶ (ofOriginal J p χ).obj b) (hτ : (projection J p χ).IsHomLift (k ≫ f) τ),
      let value := @factor _ _ _ _ J p χ a b R S f φ hφ c k τ hτ
      ((projection J p χ).IsHomLift k value ∧ value ≫ (ofOriginal J p χ).map φ = τ) ∧
      ∀ r : c ⟶ (ofOriginal J p χ).obj a,
        (projection J p χ).IsHomLift k r ∧ r ≫ (ofOriginal J p χ).map φ = τ → r = value := by
  constructor
  · exact ofOriginal_isHomLift J p χ f φ hφ.toIsHomLift
  · intro c k τ hτ
    letI := hτ
    let raw : c.obj ⟶ b := Quotient.out τ
    letI : p.IsHomLift (k ≫ f) raw := representative_isHomLift J p χ (k ≫ f) τ
    let σ : c.obj ⟶ a := Functor.IsStronglyCartesian.map p f φ (g := k) rfl raw
    have hσ : p.IsHomLift k σ := Functor.IsStronglyCartesian.map_isHomLift p f φ rfl raw
    have hfac : σ ≫ φ = raw := Functor.IsStronglyCartesian.fac p f φ rfl raw
    change (((projection J p χ).IsHomLift k (Quotient.mk'' σ) ∧
      (Quotient.mk'' σ : c ⟶ (ofOriginal J p χ).obj a) ≫ (ofOriginal J p χ).map φ = τ) ∧
      ∀ r : c ⟶ (ofOriginal J p χ).obj a,
        (projection J p χ).IsHomLift k r ∧ r ≫ (ofOriginal J p χ).map φ = τ →
          r = Quotient.mk'' σ)
    constructor
    · constructor
      · exact ofOriginal_isHomLift J p χ k σ hσ
      · change Quotient.mk'' (σ ≫ φ) = τ
        rw [hfac]
        exact Quotient.out_eq τ
    · intro r hr
      letI := hr.1
      let ρ : c.obj ⟶ a := Quotient.out r
      have hρ : p.IsHomLift k ρ := representative_isHomLift J p χ k r
      have hcomp : LocallyEqual J p χ (ρ ≫ φ) (σ ≫ φ) := by
        apply Quotient.exact (s := localSetoid J p χ c.obj b)
        change (Quotient.mk'' ρ : c ⟶ (ofOriginal J p χ).obj a) ≫
            (ofOriginal J p χ).map φ = Quotient.mk'' (σ ≫ φ)
        have hrout : (Quotient.mk'' ρ : c ⟶ (ofOriginal J p χ).obj a) = r := Quotient.out_eq r
        have hσout : (Quotient.mk'' (σ ≫ φ) : c ⟶ (ofOriginal J p χ).obj b) = τ :=
          (congrArg Quotient.mk'' hfac).trans (Quotient.out_eq τ)
        exact ((congrArg (fun q : c ⟶ (ofOriginal J p χ).obj a ↦
          q ≫ (ofOriginal J p χ).map φ) hrout).trans hr.2).trans hσout.symm
      exact (Quotient.out_eq r).symm.trans
        (Quotient.sound (locallyEqual_cancel_stronglyCartesian J p χ f φ k ρ σ hρ hσ hcomp))

/-- The class of an original strongly Cartesian arrow is strongly Cartesian. -/
theorem mapIsStronglyCartesian {a b : X} {R S : C} (f : R ⟶ S) (φ : a ⟶ b)
    [hφ : p.IsStronglyCartesian f φ] :
    (projection J p χ).IsStronglyCartesian f ((ofOriginal J p χ).map φ) where
  toIsHomLift := (mapIsStronglyCartesian_laws J p χ f φ).1
  universal_property' := fun {c} k τ hτ ↦
    ⟨@factor _ _ _ _ J p χ a b R S f φ hφ c k τ hτ,
      (mapIsStronglyCartesian_laws J p χ f φ).2 c k τ hτ⟩

/-- The separated projection is fibered, with lifts induced by the original cleavage. -/
theorem isFibered : (projection J p χ).IsFibered := by
  apply Functor.IsFibered.of_exists_isStronglyCartesian
  intro a R f
  let l := χ.lift (x := a.obj) f
  exact ⟨⟨l.source⟩, Quotient.mk'' l.hom,
    @mapIsStronglyCartesian _ _ _ _ J p χ l.source a.obj R (p.obj a.obj) f l.hom l.isStronglyCartesian⟩

private theorem comparison_laws : ofOriginal J p χ ⋙ projection J p χ = p := by
  refine CategoryTheory.Functor.ext (h_obj := fun _ ↦ rfl) ?_
  intro a b f
  change p.map f = 𝟙 (p.obj a) ≫ p.map f ≫ 𝟙 (p.obj b)
  simp

/-- Local equality does not change the original strongly Cartesian source data. -/
def comparison : CartesianBasedFunctor p (projection J p χ) :=
  CartesianBasedFunctor.ofBasedFunctor
    { toFunctor := ofOriginal J p χ
      w := comparison_laws J p χ }
    (by
      intro a b φ hφ
      change (projection J p χ).IsStronglyCartesian
        ((projection J p χ).map ((ofOriginal J p χ).map φ)) ((ofOriginal J p χ).map φ)
      exact @mapIsStronglyCartesian _ _ _ _ J p χ a b (p.obj a) (p.obj b) (p.map φ) φ hφ)

end Separated

end CategoryTheory.Functor.StackificationConstruction
