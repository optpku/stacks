/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism

/-!
# Groupoids in algebraic spaces

This module bundles the object and arrow algebraic spaces of a groupoid in algebraic
spaces over a base, together with their structure maps and pointwise groupoid laws.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]

/-- A groupoid in algebraic spaces over `B` consists of object and arrow algebraic spaces,
structure maps, and pointwise groupoid laws. In `pullback s t`, the first projection is the
later arrow and the second projection is the earlier arrow. -/
structure GroupoidAlgebraicSpace (B : AlgebraicSpace S) where
  /-- The algebraic space of objects over the base. -/
  U : Over B
  /-- The algebraic space of arrows over the base. -/
  R : Over B
  /-- The source map. -/
  s : R ⟶ U
  /-- The target map. -/
  t : R ⟶ U
  /-- Composition of composable arrows. -/
  c : pullback s t ⟶ R
  /-- The identity-arrow map. -/
  e : U ⟶ R
  /-- The inverse-arrow map. -/
  i : R ⟶ R
  /-- The source of a composite is the source of its earlier arrow. -/
  comp_source : c ≫ s = pullback.snd s t ≫ s
  /-- The target of a composite is the target of its later arrow. -/
  comp_target : c ≫ t = pullback.fst s t ≫ t
  /-- Identity arrows have the specified source. -/
  identity_source : e ≫ s = 𝟙 U
  /-- Identity arrows have the specified target. -/
  identity_target : e ≫ t = 𝟙 U
  /-- Inversion exchanges source with target. -/
  inverse_source : i ≫ s = t
  /-- Inversion exchanges target with source. -/
  inverse_target : i ≫ t = s
  /-- Composition is associative on every object of points over `B`. -/
  associativity :
    ∀ {T : Over B} (a b d : T ⟶ R)
      (h_ab : a ≫ s = b ≫ t) (h_bd : b ≫ s = d ≫ t)
      (h_ab_d : (pullback.lift a b h_ab ≫ c) ≫ s = d ≫ t)
      (h_a_bd : a ≫ s = (pullback.lift b d h_bd ≫ c) ≫ t),
      pullback.lift (pullback.lift a b h_ab ≫ c) d h_ab_d ≫ c =
        pullback.lift a (pullback.lift b d h_bd ≫ c) h_a_bd ≫ c
  /-- Composing an arrow with the identity at its source does not change it. -/
  right_identity :
    ∀ {T : Over B} (a : T ⟶ R)
      (h : a ≫ s = ((a ≫ s) ≫ e) ≫ t),
      pullback.lift a ((a ≫ s) ≫ e) h ≫ c = a
  /-- Composing the identity at the target of an arrow with that arrow does not change it. -/
  left_identity :
    ∀ {T : Over B} (a : T ⟶ R)
      (h : ((a ≫ t) ≫ e) ≫ s = a ≫ t),
      pullback.lift ((a ≫ t) ≫ e) a h ≫ c = a
  /-- Composing an arrow after its inverse gives the identity at its target. -/
  inverse_comp :
    ∀ {T : Over B} (a : T ⟶ R)
      (h : a ≫ s = (a ≫ i) ≫ t),
      pullback.lift a (a ≫ i) h ≫ c = (a ≫ t) ≫ e
  /-- Composing the inverse of an arrow after it gives the identity at its source. -/
  comp_inverse :
    ∀ {T : Over B} (a : T ⟶ R)
      (h : (a ≫ i) ≫ s = a ≫ t),
      pullback.lift (a ≫ i) a h ≫ c = (a ≫ s) ≫ e

namespace GroupoidAlgebraicSpace

/-- The first identity-pullback projection has the source of the second projection. -/
private theorem discrete_comp_source {B : AlgebraicSpace S} (U : Over B) :
    (pullback.fst (𝟙 U) (𝟙 U)) ≫ (𝟙 U) = pullback.snd (𝟙 U) (𝟙 U) ≫ (𝟙 U) := by
  exact pullback.condition

/-- The first identity-pullback projection has the target of the first projection. -/
private theorem discrete_comp_target {B : AlgebraicSpace S} (U : Over B) :
    (pullback.fst (𝟙 U) (𝟙 U)) ≫ (𝟙 U) = pullback.fst (𝟙 U) (𝟙 U) ≫ (𝟙 U) := by
  rfl

/-- The identity arrow map followed by the discrete source map is the identity. -/
private theorem discrete_identity_source {B : AlgebraicSpace S} (U : Over B) :
    (𝟙 U) ≫ (𝟙 U) = 𝟙 U := by
  simp

/-- The identity arrow map followed by the discrete target map is the identity. -/
private theorem discrete_identity_target {B : AlgebraicSpace S} (U : Over B) :
    (𝟙 U) ≫ (𝟙 U) = 𝟙 U := by
  simp

/-- The discrete inverse map followed by the source map is the target map. -/
private theorem discrete_inverse_source {B : AlgebraicSpace S} (U : Over B) :
    (𝟙 U) ≫ (𝟙 U) = (𝟙 U) := by
  simp

/-- The discrete inverse map followed by the target map is the source map. -/
private theorem discrete_inverse_target {B : AlgebraicSpace S} (U : Over B) :
    (𝟙 U) ≫ (𝟙 U) = (𝟙 U) := by
  simp

/-- Composition by the first projection of the identity pullback is associative. -/
private theorem discrete_associativity {B : AlgebraicSpace S} (U : Over B) :
    ∀ {T : Over B} (a b d : T ⟶ U)
      (h_ab : a ≫ (𝟙 U) = b ≫ (𝟙 U)) (h_bd : b ≫ (𝟙 U) = d ≫ (𝟙 U))
      (h_ab_d : (pullback.lift a b h_ab ≫ (pullback.fst (𝟙 U) (𝟙 U))) ≫ (𝟙 U) = d ≫ (𝟙 U))
      (h_a_bd : a ≫ (𝟙 U) = (pullback.lift b d h_bd ≫ (pullback.fst (𝟙 U) (𝟙 U))) ≫ (𝟙 U)),
      pullback.lift (pullback.lift a b h_ab ≫ (pullback.fst (𝟙 U) (𝟙 U))) d h_ab_d ≫ (pullback.fst (𝟙 U) (𝟙 U)) =
        pullback.lift a (pullback.lift b d h_bd ≫ (pullback.fst (𝟙 U) (𝟙 U))) h_a_bd ≫ (pullback.fst (𝟙 U) (𝟙 U)) := by
  intro T a b d h_ab h_bd h_ab_d h_a_bd
  simp [pullback.lift_fst]

/-- The discrete composition has a right identity. -/
private theorem discrete_right_identity {B : AlgebraicSpace S} (U : Over B) :
    ∀ {T : Over B} (a : T ⟶ U)
      (h : a ≫ (𝟙 U) = ((a ≫ (𝟙 U)) ≫ (𝟙 U)) ≫ (𝟙 U)),
      pullback.lift a ((a ≫ (𝟙 U)) ≫ (𝟙 U)) h ≫ (pullback.fst (𝟙 U) (𝟙 U)) = a := by
  intro T a h
  exact pullback.lift_fst _ _ _

/-- The discrete composition has a left identity. -/
private theorem discrete_left_identity {B : AlgebraicSpace S} (U : Over B) :
    ∀ {T : Over B} (a : T ⟶ U)
      (h : ((a ≫ (𝟙 U)) ≫ (𝟙 U)) ≫ (𝟙 U) = a ≫ (𝟙 U)),
      pullback.lift ((a ≫ (𝟙 U)) ≫ (𝟙 U)) a h ≫ (pullback.fst (𝟙 U) (𝟙 U)) = a := by
  intro T a h
  simp [pullback.lift_fst]

/-- A discrete arrow composed after its inverse is the identity at its target. -/
private theorem discrete_inverse_comp {B : AlgebraicSpace S} (U : Over B) :
    ∀ {T : Over B} (a : T ⟶ U)
      (h : a ≫ (𝟙 U) = (a ≫ (𝟙 U)) ≫ (𝟙 U)),
      pullback.lift a (a ≫ (𝟙 U)) h ≫ (pullback.fst (𝟙 U) (𝟙 U)) = (a ≫ (𝟙 U)) ≫ (𝟙 U) := by
  intro T a h
  simp [pullback.lift_fst]

/-- The inverse of a discrete arrow composed after it is the identity at its source. -/
private theorem discrete_comp_inverse {B : AlgebraicSpace S} (U : Over B) :
    ∀ {T : Over B} (a : T ⟶ U)
      (h : (a ≫ (𝟙 U)) ≫ (𝟙 U) = a ≫ (𝟙 U)),
      pullback.lift (a ≫ (𝟙 U)) a h ≫ (pullback.fst (𝟙 U) (𝟙 U)) = (a ≫ (𝟙 U)) ≫ (𝟙 U) := by
  intro T a h
  simp [pullback.lift_fst]

/-- The discrete groupoid in algebraic spaces on an algebraic space `U` over `B`. -/
def discrete {B : AlgebraicSpace S} (U : Over B) :
    GroupoidAlgebraicSpace B where
  U := U
  R := U
  s := 𝟙 U
  t := 𝟙 U
  c := pullback.fst (𝟙 U) (𝟙 U)
  e := 𝟙 U
  i := 𝟙 U
  comp_source := by exact discrete_comp_source U
  comp_target := by exact discrete_comp_target U
  identity_source := by exact discrete_identity_source U
  identity_target := by exact discrete_identity_target U
  inverse_source := by exact discrete_inverse_source U
  inverse_target := by exact discrete_inverse_target U
  associativity := by exact discrete_associativity U
  right_identity := by exact discrete_right_identity U
  left_identity := by exact discrete_left_identity U
  inverse_comp := by exact discrete_inverse_comp U
  comp_inverse := by exact discrete_comp_inverse U

/-- The object space of the discrete groupoid is `U`. -/
theorem discrete_U {B : AlgebraicSpace S} (U : Over B) :
    (discrete U).U = U := by
  rfl

/-- The arrow space of the discrete groupoid is `U`. -/
theorem discrete_R {B : AlgebraicSpace S} (U : Over B) :
    (discrete U).R = U := by
  rfl

/-- The source map of the discrete groupoid is the identity. -/
theorem discrete_s {B : AlgebraicSpace S} (U : Over B) :
    (discrete U).s = 𝟙 U := by
  rfl

/-- The target map of the discrete groupoid is the identity. -/
theorem discrete_t {B : AlgebraicSpace S} (U : Over B) :
    (discrete U).t = 𝟙 U := by
  rfl

/-- The composition map of the discrete groupoid is the first pullback projection. -/
theorem discrete_c {B : AlgebraicSpace S} (U : Over B) :
    (discrete U).c = pullback.fst (𝟙 U) (𝟙 U) := by
  rfl

/-- The identity map of the discrete groupoid is the identity. -/
theorem discrete_e {B : AlgebraicSpace S} (U : Over B) :
    (discrete U).e = 𝟙 U := by
  rfl

/-- The inverse map of the discrete groupoid is the identity. -/
theorem discrete_i {B : AlgebraicSpace S} (U : Over B) :
    (discrete U).i = 𝟙 U := by
  rfl

/-- Compose two `T`-valued arrows whose source and target agree. -/
def compose {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over B} (a b : T ⟶ G.R) (h : a ≫ G.s = b ≫ G.t) : T ⟶ G.R :=
  pullback.lift a b h ≫ G.c

/-- The source of a pointwise composite is the source of its earlier arrow. -/
theorem compose_source {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over B} (a b : T ⟶ G.R)
    (h : a ≫ G.s = b ≫ G.t) :
    G.compose a b h ≫ G.s = b ≫ G.s := by
  simp [compose, Category.assoc, G.comp_source, pullback.lift_snd_assoc]

/-- The target of a pointwise composite is the target of its later arrow. -/
theorem compose_target {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over B} (a b : T ⟶ G.R)
    (h : a ≫ G.s = b ≫ G.t) :
    G.compose a b h ≫ G.t = a ≫ G.t := by
  simp [compose, Category.assoc, G.comp_target, pullback.lift_fst_assoc]

/-- Cancelling a later arrow in a pointwise composite, using its inverse. -/
private theorem compose_left_cancel {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over B} (a b d : T ⟶ G.R)
    (hab : a ≫ G.s = b ≫ G.t) (had : a ≫ G.s = d ≫ G.t)
    (h : G.compose a b hab = G.compose a d had) : b = d := by
  have hi : (a ≫ G.i) ≫ G.s = a ≫ G.t := by
    simp [Category.assoc, G.inverse_source]
  have undo (b : T ⟶ G.R) (hab : a ≫ G.s = b ≫ G.t) :
      G.compose (a ≫ G.i) (G.compose a b hab)
        (hi.trans (G.compose_target a b hab).symm) = b := by
    have hcomp : G.compose (a ≫ G.i) a hi = (a ≫ G.s) ≫ G.e :=
      G.comp_inverse a hi
    have hb : G.compose (a ≫ G.i) a hi ≫ G.s = b ≫ G.t :=
      (G.compose_source _ _ _).trans hab
    calc
      _ = G.compose (G.compose (a ≫ G.i) a hi) b hb :=
        (G.associativity (a ≫ G.i) a b hi hab hb
          (hi.trans (G.compose_target a b hab).symm)).symm
      _ = b := by
        change pullback.lift (G.compose (a ≫ G.i) a hi) b hb ≫ G.c = b
        simpa only [hcomp, hab] using
          G.left_identity b (by simp [Category.assoc, G.identity_source])
  exact (undo b hab).symm.trans (by simpa only [h] using undo d had)

/-- A morphism between two scheme-valued objects of a groupoid in algebraic spaces. -/
structure PointHom {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B)
    (x y : Over.mk σ ⟶ G.U) where
  /-- The underlying scheme-valued arrow. -/
  arrow : Over.mk σ ⟶ G.R
  /-- The arrow has source `x`. -/
  source : arrow ≫ G.s = x
  /-- The arrow has target `y`. -/
  target : arrow ≫ G.t = y

namespace PointHom

/-- Construct a pointwise morphism from an arrow with specified endpoints. -/
def ofArrow {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B} {x y : Over.mk σ ⟶ G.U}
    (arrow : Over.mk σ ⟶ G.R) (source : arrow ≫ G.s = x)
    (target : arrow ≫ G.t = y) : G.PointHom σ x y :=
  ⟨arrow, source, target⟩

/-- The underlying arrow of `ofArrow` is the supplied arrow. -/
theorem ofArrow_arrow {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B}
    {x y : Over.mk σ ⟶ G.U} (arrow : Over.mk σ ⟶ G.R)
    (source : arrow ≫ G.s = x) (target : arrow ≫ G.t = y) :
    (ofArrow arrow source target).arrow = arrow := by
  rfl

/-- The endpoint equations of a pointwise morphism constructed by `ofArrow`. -/
theorem ofArrow_spec {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B}
    {x y : Over.mk σ ⟶ G.U} (arrow : Over.mk σ ⟶ G.R)
    (source : arrow ≫ G.s = x) (target : arrow ≫ G.t = y) :
    (ofArrow arrow source target).arrow ≫ G.s = x ∧
      (ofArrow arrow source target).arrow ≫ G.t = y := by
  exact ⟨source, target⟩

/-- Pointwise morphisms with the same underlying arrow are equal. -/
theorem ext {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B} {x y : Over.mk σ ⟶ G.U}
    {f g : G.PointHom σ x y} (h : f.arrow = g.arrow) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The identity arrow at a point has that point as its source. -/
private theorem id_source {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B) (x : Over.mk σ ⟶ G.U) :
    (x ≫ G.e) ≫ G.s = x := by
  simp [Category.assoc, G.identity_source]

/-- The identity arrow at a point has that point as its target. -/
private theorem id_target {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B) (x : Over.mk σ ⟶ G.U) :
    (x ≫ G.e) ≫ G.t = x := by
  simp [Category.assoc, G.identity_target]

/-- The identity pointwise morphism is induced by the identity-arrow map. -/
def id {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B) (x : Over.mk σ ⟶ G.U) :
    G.PointHom σ x x where
  arrow := x ≫ G.e
  source := by exact id_source σ x
  target := by exact id_target σ x

/-- A composite of pointwise arrows has the source of its first arrow. -/
private theorem comp_source {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B}
    {x y z : Over.mk σ ⟶ G.U} (f : G.PointHom σ x y) (g : G.PointHom σ y z) :
    G.compose g.arrow f.arrow (g.source.trans f.target.symm) ≫ G.s = x := by
  exact (G.compose_source _ _ _).trans f.source

/-- A composite of pointwise arrows has the target of its second arrow. -/
private theorem comp_target {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B}
    {x y z : Over.mk σ ⟶ G.U} (f : G.PointHom σ x y) (g : G.PointHom σ y z) :
    G.compose g.arrow f.arrow (g.source.trans f.target.symm) ≫ G.t = z := by
  exact (G.compose_target _ _ _).trans g.target

/-- The composite of pointwise morphisms is induced by groupoid composition. -/
def comp {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B}
    {x y z : Over.mk σ ⟶ G.U} (f : G.PointHom σ x y) (g : G.PointHom σ y z) :
    G.PointHom σ x z where
  arrow := G.compose g.arrow f.arrow (g.source.trans f.target.symm)
  source := by exact comp_source f g
  target := by exact comp_target f g

/-- The inverse of a pointwise arrow has the original target as its source. -/
private theorem inv_source {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B}
    {x y : Over.mk σ ⟶ G.U} (f : G.PointHom σ x y) :
    (f.arrow ≫ G.i) ≫ G.s = y := by
  simpa only [Category.assoc, G.inverse_source] using f.target

/-- The inverse of a pointwise arrow has the original source as its target. -/
private theorem inv_target {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B}
    {x y : Over.mk σ ⟶ G.U} (f : G.PointHom σ x y) :
    (f.arrow ≫ G.i) ≫ G.t = x := by
  simpa only [Category.assoc, G.inverse_target] using f.source

/-- The inverse pointwise morphism is induced by the inverse-arrow map. -/
def inv {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B}
    {x y : Over.mk σ ⟶ G.U} (f : G.PointHom σ x y) : G.PointHom σ y x where
  arrow := f.arrow ≫ G.i
  source := by exact inv_source f
  target := by exact inv_target f

end PointHom

/-- The identity pointwise arrow is a left identity for pointwise composition. -/
private theorem pointGroupoid_id_comp_law {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B}
    {x y : Over.mk σ ⟶ G.U} (f : G.PointHom σ x y) :
    PointHom.comp (PointHom.id σ x) f = f := by
  apply PointHom.ext
  change G.compose f.arrow (x ≫ G.e) _ = f.arrow
  simpa only [compose, f.source] using
    G.right_identity f.arrow (by simp [Category.assoc, G.identity_target])

/-- The identity pointwise arrow is a right identity for pointwise composition. -/
private theorem pointGroupoid_comp_id_law {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B}
    {x y : Over.mk σ ⟶ G.U} (f : G.PointHom σ x y) :
    PointHom.comp f (PointHom.id σ y) = f := by
  apply PointHom.ext
  change G.compose (y ≫ G.e) f.arrow _ = f.arrow
  simpa only [compose, f.target] using
    G.left_identity f.arrow (by simp [Category.assoc, G.identity_source])

/-- Pointwise composition of arrows is associative. -/
private theorem pointGroupoid_assoc_law {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B}
    {w x y z : Over.mk σ ⟶ G.U} (f : G.PointHom σ w x)
    (g : G.PointHom σ x y) (h : G.PointHom σ y z) :
    PointHom.comp (PointHom.comp f g) h = PointHom.comp f (PointHom.comp g h) := by
  apply PointHom.ext
  exact (G.associativity h.arrow g.arrow f.arrow
    (h.source.trans g.target.symm) (g.source.trans f.target.symm)
    (by simp [Category.assoc, G.comp_source, pullback.lift_snd_assoc,
      g.source, f.target])
    (by simp [Category.assoc, G.comp_target, pullback.lift_fst_assoc,
      h.source, g.target])).symm

/-- Composing a pointwise inverse with its arrow gives the identity at the target. -/
private theorem pointGroupoid_inv_comp_law {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B}
    {x y : Over.mk σ ⟶ G.U} (f : G.PointHom σ x y) :
    PointHom.comp (PointHom.inv f) f = PointHom.id σ y := by
  apply PointHom.ext
  change G.compose f.arrow (f.arrow ≫ G.i) _ = y ≫ G.e
  simpa only [compose, f.target] using
    G.inverse_comp f.arrow (by simp [Category.assoc, G.inverse_target])

/-- Composing a pointwise arrow with its inverse gives the identity at the source. -/
private theorem pointGroupoid_comp_inv_law {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B}
    {x y : Over.mk σ ⟶ G.U} (f : G.PointHom σ x y) :
    PointHom.comp f (PointHom.inv f) = PointHom.id σ x := by
  apply PointHom.ext
  change G.compose (f.arrow ≫ G.i) f.arrow _ = x ≫ G.e
  simpa only [compose, f.source] using
    G.comp_inverse f.arrow (by simp [Category.assoc, G.inverse_source])

/-- The explicit groupoid structure on the scheme-valued `T`-points of a groupoid in
algebraic spaces. -/
@[reducible]
def pointGroupoid {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B) :
    CategoryTheory.Groupoid (Over.mk σ ⟶ G.U) where
  Hom := fun x y ↦ G.PointHom σ x y
  id := fun x ↦ PointHom.id (G := G) σ x
  comp := fun f g ↦ PointHom.comp f g
  id_comp := by exact pointGroupoid_id_comp_law
  comp_id := by exact pointGroupoid_comp_id_law
  assoc := by exact pointGroupoid_assoc_law
  inv := fun f ↦ PointHom.inv f
  inv_comp := by exact pointGroupoid_inv_comp_law
  comp_inv := by exact pointGroupoid_comp_inv_law

/-- The bundled groupoid of scheme-valued `T`-points of a groupoid in algebraic spaces. -/
def groupoidPoints {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B) : Grpd.{u + 1, u + 1} :=
  ⟨Over.mk σ ⟶ G.U, G.pointGroupoid σ⟩

/-- The objects of `groupoidPoints G σ` are the morphisms `Over.mk σ ⟶ G.U`. -/
theorem groupoidPoints_obj {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B) :
    (G.groupoidPoints σ : Type (u + 1)) = (Over.mk σ ⟶ G.U) := by
  rfl

/-- Scheme-valued `T`-points form a groupoid whose morphisms from `x` to `y` are arrows
`Over.mk σ ⟶ G.R` with source `x` and target `y`. -/
theorem pointGroupoid_spec {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B)
    (x y : Over.mk σ ⟶ G.U) :
    (G.pointGroupoid σ).Hom x y = G.PointHom σ x y := by
  rfl

/-- The identity and composition arrows in the point groupoid are induced by `G.e` and `G.c`. -/
theorem pointGroupoid_id_comp {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B}
    {x y z : Over.mk σ ⟶ G.U} (f : G.PointHom σ x y) (g : G.PointHom σ y z) :
    ((G.pointGroupoid σ).id x).arrow = x ≫ G.e ∧
      ((G.pointGroupoid σ).comp f g).arrow = G.compose g.arrow f.arrow
        (g.source.trans f.target.symm) := by
  exact ⟨rfl, rfl⟩

/-- The inversion arrow in the point groupoid is postcomposition with `G.i`. -/
theorem pointGroupoid_inv_arrow {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B}
    {x y : Over.mk σ ⟶ G.U} (f : G.PointHom σ x y) :
    ((G.pointGroupoid σ).inv f).arrow = f.arrow ≫ G.i := by
  rfl

/-- The canonical map between composable-arrow pullbacks induced by maps of objects and arrows. -/
def composableMap {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (obj : G.U ⟶ H.U) (arrow : G.R ⟶ H.R)
    (map_s : G.s ≫ obj = arrow ≫ H.s) (map_t : G.t ≫ obj = arrow ≫ H.t) :
    pullback G.s G.t ⟶ pullback H.s H.t :=
  pullback.map G.s G.t H.s H.t arrow arrow obj map_s map_t

/-- The first projection of `composableMap` is the arrow map after the first projection. -/
theorem composableMap_fst {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (obj : G.U ⟶ H.U) (arrow : G.R ⟶ H.R)
    (map_s : G.s ≫ obj = arrow ≫ H.s) (map_t : G.t ≫ obj = arrow ≫ H.t) :
    composableMap obj arrow map_s map_t ≫ pullback.fst H.s H.t =
      pullback.fst G.s G.t ≫ arrow := by
  exact pullback.lift_fst _ _ _

/-- The second projection of `composableMap` is the arrow map after the second projection. -/
theorem composableMap_snd {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (obj : G.U ⟶ H.U) (arrow : G.R ⟶ H.R)
    (map_s : G.s ≫ obj = arrow ≫ H.s) (map_t : G.t ≫ obj = arrow ≫ H.t) :
    composableMap obj arrow map_s map_t ≫ pullback.snd H.s H.t =
      pullback.snd G.s G.t ≫ arrow := by
  exact pullback.lift_snd _ _ _

/-- A morphism of groupoids in algebraic spaces consists of compatible maps on objects and
arrows. -/
structure Hom {B : AlgebraicSpace S} (G H : GroupoidAlgebraicSpace B) where
  /-- The map on objects. -/
  obj : G.U ⟶ H.U
  /-- The map on arrows. -/
  arrow : G.R ⟶ H.R
  /-- Compatibility with source. -/
  map_s : G.s ≫ obj = arrow ≫ H.s
  /-- Compatibility with target. -/
  map_t : G.t ≫ obj = arrow ≫ H.t
  /-- Compatibility with composition. -/
  map_c : G.c ≫ arrow = composableMap obj arrow map_s map_t ≫ H.c

namespace Hom

/-- Identity maps on objects and arrows commute with the source map. -/
private theorem id_map_s {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    G.s ≫ 𝟙 G.U = 𝟙 G.R ≫ G.s := by
  simp

/-- Identity maps on objects and arrows commute with the target map. -/
private theorem id_map_t {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    G.t ≫ 𝟙 G.U = 𝟙 G.R ≫ G.t := by
  simp

/-- Identity maps on objects and arrows commute with the composition map. -/
private theorem id_map_c {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    G.c ≫ 𝟙 G.R = GroupoidAlgebraicSpace.composableMap (𝟙 G.U) (𝟙 G.R)
      (id_map_s G) (id_map_t G) ≫ G.c := by
  simp [GroupoidAlgebraicSpace.composableMap]

/-- The identity morphism of a groupoid in algebraic spaces. -/
def id {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) : Hom G G where
  obj := 𝟙 G.U
  arrow := 𝟙 G.R
  map_s := by exact id_map_s G
  map_t := by exact id_map_t G
  map_c := by exact id_map_c G

/-- The object component of the identity morphism is the identity. -/
theorem id_obj {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    (id G).obj = 𝟙 G.U := by
  rfl

/-- The arrow component of the identity morphism is the identity. -/
theorem id_arrow {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    (id G).arrow = 𝟙 G.R := by
  rfl

/-- Composite object and arrow maps commute with the source maps. -/
private theorem comp_map_s {B : AlgebraicSpace S} {G H K : GroupoidAlgebraicSpace B}
    (f : Hom G H) (g : Hom H K) :
    G.s ≫ (f.obj ≫ g.obj) = (f.arrow ≫ g.arrow) ≫ K.s := by
  rw [← Category.assoc, f.map_s, Category.assoc, g.map_s, Category.assoc]

/-- Composite object and arrow maps commute with the target maps. -/
private theorem comp_map_t {B : AlgebraicSpace S} {G H K : GroupoidAlgebraicSpace B}
    (f : Hom G H) (g : Hom H K) :
    G.t ≫ (f.obj ≫ g.obj) = (f.arrow ≫ g.arrow) ≫ K.t := by
  rw [← Category.assoc, f.map_t, Category.assoc, g.map_t, Category.assoc]

/-- Composite object and arrow maps commute with the composition maps. -/
private theorem comp_map_c {B : AlgebraicSpace S} {G H K : GroupoidAlgebraicSpace B}
    (f : Hom G H) (g : Hom H K) :
    G.c ≫ (f.arrow ≫ g.arrow) =
      GroupoidAlgebraicSpace.composableMap (f.obj ≫ g.obj) (f.arrow ≫ g.arrow)
        (comp_map_s f g) (comp_map_t f g) ≫ K.c := by
  rw [← Category.assoc, f.map_c, Category.assoc, g.map_c, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp [Category.assoc, GroupoidAlgebraicSpace.composableMap,
      pullback.lift_fst_assoc, pullback.lift_fst]
  · simp [Category.assoc, GroupoidAlgebraicSpace.composableMap,
      pullback.lift_snd_assoc, pullback.lift_snd]

/-- Composition of morphisms of groupoids in algebraic spaces. -/
def comp {B : AlgebraicSpace S} {G H K : GroupoidAlgebraicSpace B}
    (f : Hom G H) (g : Hom H K) : Hom G K where
  obj := f.obj ≫ g.obj
  arrow := f.arrow ≫ g.arrow
  map_s := by exact comp_map_s f g
  map_t := by exact comp_map_t f g
  map_c := by exact comp_map_c f g

/-- The object component of a composite is the composite of the object components. -/
theorem comp_obj {B : AlgebraicSpace S} {G H K : GroupoidAlgebraicSpace B}
    (f : Hom G H) (g : Hom H K) : (comp f g).obj = f.obj ≫ g.obj := by
  rfl

/-- The arrow component of a composite is the composite of the arrow components. -/
theorem comp_arrow {B : AlgebraicSpace S} {G H K : GroupoidAlgebraicSpace B}
    (f : Hom G H) (g : Hom H K) : (comp f g).arrow = f.arrow ≫ g.arrow := by
  rfl

/-- Morphisms of groupoids in algebraic spaces are determined by their object and arrow maps. -/
theorem ext {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    {f g : Hom G H} (h_obj : f.obj = g.obj) (h_arrow : f.arrow = g.arrow) : f = g := by
  cases f
  cases g
  cases h_obj
  cases h_arrow
  rfl

/-- Compatibility with composition evaluated on any object of points over the base. -/
private theorem map_compose {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) {T : Over B} (a b : T ⟶ G.R)
    (h : a ≫ G.s = b ≫ G.t)
    (h' : (a ≫ f.arrow) ≫ H.s = (b ≫ f.arrow) ≫ H.t) :
    G.compose a b h ≫ f.arrow = H.compose (a ≫ f.arrow) (b ≫ f.arrow) h' := by
  unfold GroupoidAlgebraicSpace.compose
  rw [Category.assoc, f.map_c, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp [Category.assoc, GroupoidAlgebraicSpace.composableMap,
      pullback.lift_fst_assoc, pullback.lift_fst]
  · simp [Category.assoc, GroupoidAlgebraicSpace.composableMap,
      pullback.lift_snd_assoc, pullback.lift_snd]

/-- A morphism of groupoids in algebraic spaces preserves identity arrows. -/
theorem map_e {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) : G.e ≫ f.arrow = f.obj ≫ H.e := by
  have hs : (G.e ≫ f.arrow) ≫ H.s = f.obj := by
    rw [Category.assoc, ← f.map_s, ← Category.assoc, G.identity_source,
      Category.id_comp]
  have ht : (G.e ≫ f.arrow) ≫ H.t = f.obj := by
    rw [Category.assoc, ← f.map_t, ← Category.assoc, G.identity_target,
      Category.id_comp]
  have hG : G.e ≫ G.s = G.e ≫ G.t :=
    G.identity_source.trans G.identity_target.symm
  have hGG : G.compose G.e G.e hG = G.e := by
    simpa only [GroupoidAlgebraicSpace.compose, G.identity_source,
      Category.id_comp] using G.right_identity G.e
        (by simp [Category.assoc, G.identity_source, G.identity_target])
  have hHH : H.compose (G.e ≫ f.arrow) (G.e ≫ f.arrow) (hs.trans ht.symm) =
      G.e ≫ f.arrow := by
    rw [← map_compose f G.e G.e hG (hs.trans ht.symm), hGG]
  have hid : (G.e ≫ f.arrow) ≫ H.s =
      (((G.e ≫ f.arrow) ≫ H.s) ≫ H.e) ≫ H.t := by
    simp [Category.assoc, H.identity_target]
  have hc := compose_left_cancel H (G.e ≫ f.arrow) (G.e ≫ f.arrow)
    (((G.e ≫ f.arrow) ≫ H.s) ≫ H.e) (hs.trans ht.symm) hid
    (hHH.trans (H.right_identity (G.e ≫ f.arrow) hid).symm)
  simpa only [hs] using hc

/-- A morphism of groupoids in algebraic spaces preserves inverse arrows. -/
theorem map_i {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) : G.i ≫ f.arrow = f.arrow ≫ H.i := by
  have hab : f.arrow ≫ H.s = (G.i ≫ f.arrow) ≫ H.t := by
    rw [Category.assoc, ← f.map_t, ← Category.assoc, G.inverse_target, f.map_s]
  have had : f.arrow ≫ H.s = (f.arrow ≫ H.i) ≫ H.t := by
    simp [Category.assoc, H.inverse_target]
  have hG : (𝟙 G.R) ≫ G.s = G.i ≫ G.t := by
    simp [G.inverse_target]
  have hi : G.compose (𝟙 G.R) G.i hG = G.t ≫ G.e := by
    simpa only [GroupoidAlgebraicSpace.compose, Category.id_comp] using
      G.inverse_comp (𝟙 G.R) (by simp [G.inverse_target])
  have hm : H.compose f.arrow (G.i ≫ f.arrow) hab =
      (f.arrow ≫ H.t) ≫ H.e := by
    calc
      _ = G.compose (𝟙 G.R) G.i hG ≫ f.arrow := by
        simpa only [Category.id_comp] using
          (map_compose f (𝟙 G.R) G.i hG (by simpa only [Category.id_comp] using hab)).symm
      _ = (G.t ≫ G.e) ≫ f.arrow := by rw [hi]
      _ = (f.arrow ≫ H.t) ≫ H.e := by
        rw [Category.assoc, f.map_e, ← Category.assoc, f.map_t]
  exact compose_left_cancel H f.arrow (G.i ≫ f.arrow) (f.arrow ≫ H.i) hab had
    (hm.trans (H.inverse_comp f.arrow had).symm)

/-- The induced map on pullbacks of the source and target maps. -/
def composableMap {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) : pullback G.s G.t ⟶ pullback H.s H.t :=
  GroupoidAlgebraicSpace.composableMap f.obj f.arrow f.map_s f.map_t

/-- The first projection of `f.composableMap` is the arrow map after the first projection. -/
theorem composableMap_fst {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) :
    f.composableMap ≫ pullback.fst H.s H.t = pullback.fst G.s G.t ≫ f.arrow := by
  exact GroupoidAlgebraicSpace.composableMap_fst f.obj f.arrow f.map_s f.map_t

/-- The second projection of `f.composableMap` is the arrow map after the second projection. -/
theorem composableMap_snd {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) :
    f.composableMap ≫ pullback.snd H.s H.t = pullback.snd G.s G.t ≫ f.arrow := by
  exact GroupoidAlgebraicSpace.composableMap_snd f.obj f.arrow f.map_s f.map_t

/-- Postcomposition with a groupoid morphism's arrow map preserves sources. -/
private theorem mapPoints_source {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B}
    {x y : Over.mk σ ⟶ G.U} (p : G.PointHom σ x y) :
    (p.arrow ≫ f.arrow) ≫ H.s = x ≫ f.obj := by
  rw [Category.assoc, ← f.map_s, ← Category.assoc, p.source]

/-- Postcomposition with a groupoid morphism's arrow map preserves targets. -/
private theorem mapPoints_target {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B}
    {x y : Over.mk σ ⟶ G.U} (p : G.PointHom σ x y) :
    (p.arrow ≫ f.arrow) ≫ H.t = y ≫ f.obj := by
  rw [Category.assoc, ← f.map_t, ← Category.assoc, p.target]

/-- A groupoid morphism sends a pointwise arrow to its postcomposition with the arrow map. -/
private def mapPointsArrow {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B}
    {x y : Over.mk σ ⟶ G.U} (p : G.PointHom σ x y) :
    H.PointHom σ (x ≫ f.obj) (y ≫ f.obj) where
  arrow := p.arrow ≫ f.arrow
  source := by exact mapPoints_source f p
  target := by exact mapPoints_target f p

/-- Postcomposition of pointwise arrows preserves identity arrows. -/
private theorem mapPoints_map_id {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B)
    (x : Over.mk σ ⟶ G.U) :
    mapPointsArrow f (PointHom.id σ x) = PointHom.id σ (x ≫ f.obj) := by
  apply PointHom.ext
  change (x ≫ G.e) ≫ f.arrow = (x ≫ f.obj) ≫ H.e
  rw [Category.assoc, f.map_e, Category.assoc]

/-- Postcomposition of pointwise arrows preserves composition. -/
private theorem mapPoints_map_comp {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B}
    {x y z : Over.mk σ ⟶ G.U} (p : G.PointHom σ x y) (q : G.PointHom σ y z) :
    mapPointsArrow f (PointHom.comp p q) =
      PointHom.comp (mapPointsArrow f p) (mapPointsArrow f q) := by
  apply PointHom.ext
  change (G.compose q.arrow p.arrow _) ≫ f.arrow =
    H.compose (q.arrow ≫ f.arrow) (p.arrow ≫ f.arrow) _
  exact map_compose f q.arrow p.arrow _ _

/-- The functor of scheme-valued point groupoids induced by a morphism of groupoids in
algebraic spaces. -/
def mapPoints {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) {T : Over S} (σ : AlgebraicSpace.ofOver T ⟶ B) :
    G.groupoidPoints σ ⟶ H.groupoidPoints σ where
  obj := fun x ↦ x ≫ f.obj
  map := fun p ↦
    { arrow := p.arrow ≫ f.arrow
      source := by exact mapPoints_source f p
      target := by exact mapPoints_target f p }
  map_id := by exact mapPoints_map_id f σ
  map_comp := by exact mapPoints_map_comp f

/-- On objects, the induced functor on points is postcomposition with the object map. -/
theorem mapPoints_obj {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) {T : Over S}
    (σ : AlgebraicSpace.ofOver T ⟶ B) (x : Over.mk σ ⟶ G.U) :
    (f.mapPoints σ).obj x = x ≫ f.obj := by
  rfl

/-- On arrows, the induced functor on points is postcomposition with the arrow map. -/
theorem mapPoints_map_arrow {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) {T : Over S}
    (σ : AlgebraicSpace.ofOver T ⟶ B) {x y : Over.mk σ ⟶ G.U}
    (p : G.PointHom σ x y) :
    ((f.mapPoints σ).map p).arrow = p.arrow ≫ f.arrow := by
  rfl

/-- The object and arrow components of the functor induced on point groupoids. -/
theorem mapPoints_spec {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) {T : Over S}
    (σ : AlgebraicSpace.ofOver T ⟶ B) (x : Over.mk σ ⟶ G.U)
    {y : Over.mk σ ⟶ G.U} (p : G.PointHom σ x y) :
    (f.mapPoints σ).obj x = x ≫ f.obj ∧
      ((f.mapPoints σ).map p).arrow = p.arrow ≫ f.arrow := by
  exact ⟨rfl, rfl⟩

end Hom

end GroupoidAlgebraicSpace

end AlgebraicGeometry
