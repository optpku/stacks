/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import Mathlib.CategoryTheory.EquivalenceRelation
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Subobject.MonoOver
public import ReasLib.CategoryTheory.Limits.Over.Products

/-!
# Relations on an algebraic space over a base

This module records pre-relations and relations in the slice category of algebraic spaces over a
base algebraic space.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]

-- Use mathlib's proved slice-product instance; the imported ReasLib owner is still unproved.
attribute [local instance] Over.ConstructProducts.over_binaryProduct_of_pullback

/-- A pre-relation on `U` over `B` is an object over `U ⨯ U` in `Over B`. -/
abbrev PreRelation {B : AlgebraicSpace S} (U : Over B) :=
  Over (U ⨯ U)

namespace PreRelation

/-- Construct a pre-relation from its source object and its map to `U ⨯ U`. -/
def ofHom {B : AlgebraicSpace S} {U R : Over B} (j : R ⟶ U ⨯ U) : PreRelation U :=
  Over.mk j

/-- The structure morphism of the pre-relation constructed from `j` is `j`. -/
theorem ofHom_hom {B : AlgebraicSpace S} {U R : Over B} (j : R ⟶ U ⨯ U) :
    (ofHom j).hom = j := rfl

/-- The first projection of a pre-relation. -/
def t {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) : P.left ⟶ U :=
  P.hom ≫ prod.fst

/-- The second projection of a pre-relation. -/
def s {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) : P.left ⟶ U :=
  P.hom ≫ prod.snd

/-- The map defining a pre-relation is the product lift of its two projections. -/
theorem hom_eq_prod_lift {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) :
    P.hom = prod.lift P.t P.s := by
  apply prod.hom_ext
  · simpa [t] using (prod.lift_fst P.t P.s).symm
  · simpa [s] using (prod.lift_snd P.t P.s).symm

/-- The map on `T/B`-valued points induced by the two projections of a pre-relation. -/
def pointMap {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) (T : Over B) :
    (T ⟶ P.left) → (T ⟶ U) × (T ⟶ U) :=
  fun r ↦ (r ≫ P.t, r ≫ P.s)

/-- The point map sends `r` to its composites with the two projections. -/
theorem pointMap_apply {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)
    (T : Over B) (r : T ⟶ P.left) :
    P.pointMap T r = (r ≫ P.t, r ≫ P.s) := rfl

/-- The image relation on the `T/B`-valued points of `U`. -/
def pointRel {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) (T : Over B) :
    (T ⟶ U) → (T ⟶ U) → Prop :=
  fun x y ↦ ∃ r : T ⟶ P.left, r ≫ P.t = x ∧ r ≫ P.s = y

/-- Two `T/B`-valued points are related exactly when they lift to a point of the source. -/
theorem pointRel_iff {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)
    (T : Over B) (x y : T ⟶ U) :
    P.pointRel T x y ↔ ∃ r : T ⟶ P.left, r ≫ P.t = x ∧ r ≫ P.s = y := Iff.rfl

/-- A pre-relation is a pre-equivalence relation when the image of `j` on `T`-valued points is
an equivalence relation for every scheme `T` over `B`. -/
def IsPreEquivalence {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) : Prop :=
  ∀ (T : Over S) (σ : ofOver T ⟶ B), Equivalence (P.pointRel (Over.mk σ))

/-- The pointwise characterization of a pre-equivalence relation on scheme-valued points over `B`. -/
theorem isPreEquivalence_iff {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) :
    P.IsPreEquivalence ↔
      ∀ (T : Over S) (σ : ofOver T ⟶ B), Equivalence (P.pointRel (Over.mk σ)) := by
  rfl

omit [HasPullbacks (AlgebraicSpace S)] in
private theorem injective_app_of_mono {X Y : AlgebraicSpace S} (i : X ⟶ Y) [Mono i]
    (T : (Over S)ᵒᵖ) : Function.Injective (i.app T) := by
  intro a b hab
  let a' : ofOver T.unop ⟶ X := yonedaEquiv.symm a
  let b' : ofOver T.unop ⟶ X := yonedaEquiv.symm b
  have hab' : a' ≫ i = b' ≫ i := by
    apply (yonedaEquiv (C := Over S) (X := T.unop) (F := Y.functorOfPoints)).injective
    change yonedaEquiv
      (NatTrans.vcomp ((yonedaEquiv (C := Over S) (X := T.unop)
        (F := X.functorOfPoints)).symm a) i) = yonedaEquiv
      (NatTrans.vcomp ((yonedaEquiv (C := Over S) (X := T.unop)
        (F := X.functorOfPoints)).symm b) i)
    simpa [yonedaEquiv] using hab
  have heq : a' = b' := (cancel_mono i).1 hab'
  have := congrArg
    (fun k : ofOver T.unop ⟶ X =>
      (yonedaEquiv (C := Over S) (X := T.unop) (F := X.functorOfPoints)) k) heq
  simpa only [a', b', Equiv.apply_symm_apply] using this

omit [HasPullbacks (AlgebraicSpace S)] in
/-- Unique scheme-valued factorizations through a monomorphism assemble naturally. -/
private theorem exists_factor_of_schemePoints {B : AlgebraicSpace S} {X Y Z : Over B}
    (i : Y ⟶ Z) [Mono i] (f : X ⟶ Z)
    (h : ∀ (T : Over S) (σ : ofOver T ⟶ B) (x : Over.mk σ ⟶ X),
      ∃ y : Over.mk σ ⟶ Y, y ≫ i = x ≫ f) :
    ∃ g : X ⟶ Y, g ≫ i = f := by
  have lifts : ∀ (T : (Over S)ᵒᵖ) (x : X.left.functorOfPoints.obj T),
      ∃ y : Y.left.functorOfPoints.obj T, i.left.app T y = f.left.app T x := by
    intro T x
    let x' : ofOver T.unop ⟶ X.left := yonedaEquiv.symm x
    let σ : ofOver T.unop ⟶ B := x' ≫ X.hom
    obtain ⟨y, hy⟩ := h T.unop σ (Over.homMk x' rfl)
    refine ⟨(yonedaEquiv (C := Over S) (X := T.unop)
      (F := Y.left.functorOfPoints)) y.left, ?_⟩
    have hy' := congrArg
      (fun k : Over.mk σ ⟶ Z =>
        (yonedaEquiv (C := Over S) (X := T.unop)
          (F := Z.left.functorOfPoints)) k.left) hy
    change yonedaEquiv (NatTrans.vcomp y.left i.left) =
      yonedaEquiv (NatTrans.vcomp (yonedaEquiv.symm x) f.left) at hy'
    simpa [yonedaEquiv] using hy'
  choose g hg using lifts
  let φ : X.left ⟶ Y.left := {
    app := fun T => TypeCat.ofHom (g T)
    naturality := by
      intro T T' a
      apply ConcreteCategory.hom_ext
      intro x
      apply injective_app_of_mono i.left T'
      change i.left.app T' (g T' (X.left.functorOfPoints.map a x)) =
        i.left.app T' (Y.left.functorOfPoints.map a (g T x))
      calc
        i.left.app T' (g T' (X.left.functorOfPoints.map a x)) =
            f.left.app T' (X.left.functorOfPoints.map a x) := hg _ _
        _ = Z.left.functorOfPoints.map a (f.left.app T x) :=
          NatTrans.naturality_apply f.left a x
        _ = Z.left.functorOfPoints.map a (i.left.app T (g T x)) :=
          congrArg (Z.left.functorOfPoints.map a) (hg T x).symm
        _ = i.left.app T' (Y.left.functorOfPoints.map a (g T x)) :=
          (NatTrans.naturality_apply i.left a (g T x)).symm }
  have hφ : φ ≫ i.left = f.left := by
    change NatTrans.vcomp φ i.left = f.left
    apply NatTrans.ext
    funext T
    exact ConcreteCategory.hom_ext _ _ (hg T)
  have hbase : φ ≫ Y.hom = X.hom := by
    calc
      φ ≫ Y.hom = φ ≫ i.left ≫ Z.hom := by rw [i.w]
      _ = (φ ≫ i.left) ≫ Z.hom := (Category.assoc _ _ _).symm
      _ = f.left ≫ Z.hom := by rw [hφ]
      _ = X.hom := f.w
  refine ⟨Over.homMk φ hbase, ?_⟩
  apply Over.OverMorphism.ext
  exact hφ

private theorem pointRel_of_schemePoints {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) [Mono P.hom] {T : Over B} (x y : T ⟶ U)
    (h : ∀ (T' : Over S) (σ : ofOver T' ⟶ B) (f : Over.mk σ ⟶ T),
      P.pointRel (Over.mk σ) (f ≫ x) (f ≫ y)) : P.pointRel T x y := by
  obtain ⟨r, hr⟩ := exists_factor_of_schemePoints P.hom (prod.lift x y) (by
    intro T' σ f
    obtain ⟨r, hr₁, hr₂⟩ := h T' σ f
    refine ⟨r, prod.hom_ext ?_ ?_⟩
    · simpa only [Category.assoc, prod.lift_fst, t] using hr₁
    · simpa only [Category.assoc, prod.lift_snd, s] using hr₂)
  refine ⟨r, ?_, ?_⟩
  · simpa only [Category.assoc, prod.lift_fst, t] using
      congrArg (fun k => k ≫ prod.fst) hr
  · simpa only [Category.assoc, prod.lift_snd, s] using
      congrArg (fun k => k ≫ prod.snd) hr

private theorem pointRel_precomp {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {T T' : Over B} {x y : T ⟶ U}
    (h : P.pointRel T x y) (f : T' ⟶ T) : P.pointRel T' (f ≫ x) (f ≫ y) := by
  obtain ⟨r, hr₁, hr₂⟩ := h
  exact ⟨f ≫ r, by simp [Category.assoc, hr₁], by simp [Category.assoc, hr₂]⟩

/-- Under a monic defining map, a pre-equivalence relation is equivalently tested on all
algebraic spaces over `B`. -/
theorem isPreEquivalence_iff_points {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) [Mono P.hom] :
    P.IsPreEquivalence ↔ ∀ T : Over B, Equivalence (P.pointRel T) := by
  constructor
  · intro h T
    refine ⟨?_, ?_, ?_⟩
    · intro x
      apply pointRel_of_schemePoints P x x
      intro T' σ f
      exact (h T' σ).refl (f ≫ x)
    · intro x y hxy
      apply pointRel_of_schemePoints P y x
      intro T' σ f
      exact (h T' σ).symm (pointRel_precomp P hxy f)
    · intro x y z hxy hyz
      apply pointRel_of_schemePoints P x z
      intro T' σ f
      exact (h T' σ).trans (pointRel_precomp P hxy f) (pointRel_precomp P hyz f)
  · intro h T σ
    exact h (Over.mk σ)

/-- An equivalence relation has injective point maps and equivalence-relation image relations on
all scheme-valued points over the base. -/
def IsEquivalence {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) : Prop :=
  ∀ (T : Over S) (σ : ofOver T ⟶ B),
    Function.Injective (P.pointMap (Over.mk σ)) ∧
      Equivalence (P.pointRel (Over.mk σ))

end PreRelation

/-- A relation on `U` over `B` is a monomorphism into `U ⨯ U` in `Over B`. -/
abbrev Relation {B : AlgebraicSpace S} (U : Over B) :=
  MonoOver (U ⨯ U)

namespace Relation

/-- Forget the monomorphism property of a relation. -/
def toPreRelation {B : AlgebraicSpace S} {U : Over B} (Q : Relation U) : PreRelation U :=
  Q.obj

/-- Forgetting a relation preserves its defining arrow. -/
theorem toPreRelation_hom {B : AlgebraicSpace S} {U : Over B} (Q : Relation U) :
    Q.toPreRelation.hom = Q.arrow := rfl

/-- Regard a pre-relation with monic defining arrow as a relation. -/
def ofPreRelation {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)
    [Mono P.hom] : Relation U :=
  MonoOver.mk P.hom

/-- The relation obtained from a monic pre-relation has the same defining arrow. -/
theorem ofPreRelation_arrow {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)
    [Mono P.hom] :
    (ofPreRelation P).arrow = P.hom := rfl

end Relation

namespace PreRelation

/-- A monic defining map makes the two projections of a pre-relation jointly monic. -/
instance instJointlyMono₂ {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)
    [Mono P.hom] : JointlyMono₂ P.t P.s where
  right_cancellation := by
    intro Y f g h₁ h₂
    apply (cancel_mono P.hom).1
    calc
      f ≫ P.hom = f ≫ prod.lift P.t P.s := by rw [P.hom_eq_prod_lift]
      _ = prod.lift (f ≫ P.t) (f ≫ P.s) := by simp
      _ = prod.lift (g ≫ P.t) (g ≫ P.s) := by rw [h₁, h₂]
      _ = g ≫ P.hom := by rw [P.hom_eq_prod_lift]; simp

/-- An internal equivalence relation has a monic defining map to `U ⨯ U`. -/
instance instMonoHom {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)
    [IsEquivalenceRelation P.t P.s] : Mono P.hom := by
  obtain ⟨e⟩ :=
    IsEquivalenceRelation.nonempty_equivalenceRelation (p₁ := P.t) (p₂ := P.s)
  rw [P.hom_eq_prod_lift]
  constructor
  intro Y f g h
  apply e.right_cancellation f g
  · have h' := congrArg (fun k => k ≫ prod.fst) h
    simpa only [Category.assoc, prod.lift_fst] using h'
  · have h' := congrArg (fun k => k ≫ prod.snd) h
    simpa only [Category.assoc, prod.lift_snd] using h'

/-- Internal equivalence is characterized on every algebraic space of points over the base by
injectivity of the point map and the equivalence-relation property of its image. -/
theorem isEquivalenceRelation_iff_points {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) :
    IsEquivalenceRelation P.t P.s ↔
      ∀ T : Over B, Function.Injective (P.pointMap T) ∧ Equivalence (P.pointRel T) := by
  constructor
  · intro h T
    obtain ⟨e⟩ := h.nonempty_equivalenceRelation
    constructor
    · intro f g hfg
      apply e.right_cancellation f g
      · exact congrArg Prod.fst hfg
      · exact congrArg Prod.snd hfg
    · refine ⟨?_, ?_, ?_⟩
      · intro x
        refine ⟨x ≫ e.r, ?_, ?_⟩
        · simp [Category.assoc]
        · simp [Category.assoc]
      · intro x y hxy
        rcases hxy with ⟨r, hr₁, hr₂⟩
        refine ⟨r ≫ e.s, ?_, ?_⟩
        · simp [Category.assoc, e.symmetry₁, hr₂]
        · simp [Category.assoc, e.symmetry₂, hr₁]
      · intro x y z hxy hyz
        rcases hxy with ⟨r, hr₁, hr₂⟩
        rcases hyz with ⟨r', hr₁', hr₂'⟩
        let l : T ⟶ e.c.pt := PullbackCone.IsLimit.lift e.isLimit r r' (hr₂.trans hr₁'.symm)
        refine ⟨l ≫ e.t, ?_, ?_⟩
        · calc
            (l ≫ e.t) ≫ P.t = l ≫ (e.t ≫ P.t) := by simp [Category.assoc]
            _ = l ≫ (e.c.fst ≫ P.t) := by rw [e.transitivity₁]
            _ = (l ≫ e.c.fst) ≫ P.t := (Category.assoc _ _ _).symm
            _ = r ≫ P.t := congrArg (fun k => k ≫ P.t)
              (PullbackCone.IsLimit.lift_fst e.isLimit r r' (hr₂.trans hr₁'.symm))
            _ = x := hr₁
        · calc
            (l ≫ e.t) ≫ P.s = l ≫ (e.t ≫ P.s) := by simp [Category.assoc]
            _ = l ≫ (e.c.snd ≫ P.s) := by rw [e.transitivity₂]
            _ = (l ≫ e.c.snd) ≫ P.s := (Category.assoc _ _ _).symm
            _ = r' ≫ P.s := congrArg (fun k => k ≫ P.s)
              (PullbackCone.IsLimit.lift_snd e.isLimit r r' (hr₂.trans hr₁'.symm))
            _ = z := hr₂'
  · intro h
    have hmono : Mono P.hom := by
      constructor
      intro T f g hfg
      apply (h T).1
      apply Prod.ext
      · change f ≫ P.t = g ≫ P.t
        simpa [t, Category.assoc] using congrArg (fun k => k ≫ prod.fst) hfg
      · change f ≫ P.s = g ≫ P.s
        simpa [s, Category.assoc] using congrArg (fun k => k ≫ prod.snd) hfg
    letI : Mono P.hom := hmono
    obtain ⟨r, hr₁, hr₂⟩ := (h U).2.refl (𝟙 U)
    have hsymm : P.pointRel P.left P.t P.s := ⟨𝟙 _, by simp, by simp⟩
    obtain ⟨s', hs₁, hs₂⟩ := (h P.left).2.symm hsymm
    let c : PullbackCone P.s P.t :=
      PullbackCone.mk (pullback.fst P.s P.t) (pullback.snd P.s P.t) pullback.condition
    have hxy : P.pointRel c.pt (c.fst ≫ P.t) (c.fst ≫ P.s) :=
      ⟨c.fst, by simp, by simp⟩
    have hyz : P.pointRel c.pt (c.fst ≫ P.s) (c.snd ≫ P.s) := by
      refine ⟨c.snd, c.condition.symm, by simp⟩
    obtain ⟨t', ht₁, ht₂⟩ := (h c.pt).2.trans hxy hyz
    let refl : ReflexiveRelation P.t P.s := {
      toJointlyMono₂ := inferInstance
      r := r
      reflexivity₁ := hr₁
      reflexivity₂ := hr₂ }
    let symm : SymmetricRelation P.t P.s := {
      toJointlyMono₂ := inferInstance
      s := s'
      symmetry₁ := hs₁
      symmetry₂ := hs₂ }
    let trans : TransitiveRelation P.t P.s := {
      toJointlyMono₂ := inferInstance
      c := c
      isLimit := pullbackIsPullback _ _
      t := t'
      transitivity₁ := ht₁
      transitivity₂ := ht₂ }
    exact ⟨⟨{ __ := refl, __ := symm, __ := trans }⟩⟩

/-- Internal equivalence is equivalent to being both a relation and a pre-equivalence relation. -/
theorem isEquivalenceRelation_iff {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) :
    IsEquivalenceRelation P.t P.s ↔ Mono P.hom ∧ P.IsPreEquivalence := by
  constructor
  · intro h
    letI : IsEquivalenceRelation P.t P.s := h
    refine ⟨inferInstance, ?_⟩
    intro T σ
    exact (isEquivalenceRelation_iff_points P).mp h (Over.mk σ) |>.2
  · rintro ⟨hmono, hpre⟩
    letI : Mono P.hom := hmono
    apply (isEquivalenceRelation_iff_points P).mpr
    intro T
    refine ⟨?_, (isPreEquivalence_iff_points P).mp hpre T⟩
    intro f g hfg
    exact (instJointlyMono₂ P).right_cancellation f g (congrArg Prod.fst hfg)
      (congrArg Prod.snd hfg)

/-- Internal equivalence is characterized on scheme-valued points over `B` by injectivity of the
point map and the equivalence-relation property of its image. -/
theorem isEquivalenceRelation_iff_schemePoints {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) :
    IsEquivalenceRelation P.t P.s ↔
      ∀ (T : Over S) (σ : ofOver T ⟶ B),
        Function.Injective (P.pointMap (Over.mk σ)) ∧
          Equivalence (P.pointRel (Over.mk σ)) := by
  constructor
  · intro h T σ
    exact (isEquivalenceRelation_iff_points P).mp h (Over.mk σ)
  · intro h
    have hmono : Mono P.hom := by
      constructor
      intro T f g hfg
      apply Over.OverMorphism.ext
      refine hom_ext_yoneda (C := Over S)
        (P := T.left.functorOfPoints) (Q := P.left.left.functorOfPoints) ?_
      intro T' x
      let σ : ofOver T' ⟶ B := (x : ofOver T' ⟶ T.left) ≫ T.hom
      let q : Over.mk σ ⟶ T := Over.homMk x rfl
      have heq : q ≫ f = q ≫ g := by
        apply (h T' σ).1
        apply Prod.ext
        · change (q ≫ f) ≫ P.t = (q ≫ g) ≫ P.t
          simpa only [Category.assoc, t] using
            congrArg (fun k : T ⟶ U ⨯ U => q ≫ k ≫ prod.fst) hfg
        · change (q ≫ f) ≫ P.s = (q ≫ g) ≫ P.s
          simpa only [Category.assoc, s] using
            congrArg (fun k : T ⟶ U ⨯ U => q ≫ k ≫ prod.snd) hfg
      have heq' := congrArg (fun k : Over.mk σ ⟶ P.left => k.left) heq
      change NatTrans.vcomp x f.left = NatTrans.vcomp x g.left at heq'
      exact heq'
    exact (isEquivalenceRelation_iff P).mpr ⟨hmono, fun T σ => (h T σ).2⟩

end PreRelation

end AlgebraicGeometry.AlgebraicSpace
