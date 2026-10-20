/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.PreRelation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.BaseChange

/-!
# Invariant base change of groupoids in algebraic spaces

An invariant morphism from the object space to an algebraic space gives a groupoid
over that space. Its base change, regarded over the original base, has a
pre-relation canonically isomorphic to the invariant base-changed pre-relation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

open AlgebraicSpace

/-- Triangle witnessing that the source map of `G` lies over `X` via `φ`. -/
private theorem overS_w {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) :
    G.s.left ≫ φ.left = G.toPreRelation.t.left ≫ φ.left := sorry

/-- Triangle witnessing that the target map of `G` lies over `X` via `φ`. -/
private theorem overT_w {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) :
    G.t.left ≫ φ.left = G.toPreRelation.t.left ≫ φ.left := sorry

/-- Triangle witnessing that identity arrows of `G` lie over `X` via `φ`. -/
private theorem overE_w {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) :
    G.e.left ≫ G.toPreRelation.t.left ≫ φ.left = φ.left := sorry

/-- Triangle witnessing that inversion of `G` lies over `X` via `φ`. -/
private theorem overI_w {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) :
    G.i.left ≫ G.toPreRelation.t.left ≫ φ.left =
      G.toPreRelation.t.left ≫ φ.left := sorry

/-- The object space of `G`, regarded over `X` along an invariant morphism `φ`. -/
def overU {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) : Over X.left :=
  Over.mk φ.left

/-- The arrow space of `G`, regarded over `X` along an invariant morphism `φ`. -/
def overR {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) : Over X.left :=
  Over.mk (G.toPreRelation.t.left ≫ φ.left)

/-- The source map of `G`, as a morphism over `X`. -/
def overS {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) :
    overR G φ ⟶ overU G φ :=
  Over.homMk G.s.left (by exact overS_w G φ hφ)

/-- The target map of `G`, as a morphism over `X`. -/
def overT {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) :
    overR G φ ⟶ overU G φ :=
  Over.homMk G.t.left (by exact overT_w G φ hφ)

/-- The identity-arrow map of `G`, as a morphism over `X`. -/
def overE {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) :
    overU G φ ⟶ overR G φ :=
  Over.homMk G.e.left (by exact overE_w G φ hφ)

/-- The inverse-arrow map of `G`, as a morphism over `X`. -/
def overI {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) :
    overR G φ ⟶ overR G φ :=
  Over.homMk G.i.left (by exact overI_w G φ hφ)

/-- Triangle witnessing that composition of `G` lies over `X` via `φ`. -/
private theorem overComposable_w {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) :
    ((PreservesPullback.iso (Over.forget X.left) (overS G φ hφ) (overT G φ hφ)).hom ≫
          (PreservesPullback.iso (Over.forget B) G.s G.t).inv ≫ G.c.left) ≫
        (overR G φ).hom =
      (pullback (overS G φ hφ) (overT G φ hφ)).hom := sorry

/-- Composition of composable arrows of `G`, as a morphism over `X`. -/
def overComposable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) :
    pullback (overS G φ hφ) (overT G φ hφ) ⟶ overR G φ :=
  Over.homMk
    ((PreservesPullback.iso (Over.forget X.left) (overS G φ hφ) (overT G φ hφ)).hom ≫
      (PreservesPullback.iso (Over.forget B) G.s G.t).inv ≫ G.c.left)
    (by exact overComposable_w G φ hφ)

/-- Regard a groupoid in algebraic spaces over `B` as a groupoid over `X` along an
invariant morphism `φ : U ⟶ X`. -/
def over {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) :
    GroupoidAlgebraicSpace X.left where
  U := overU G φ
  R := overR G φ
  s := overS G φ hφ
  t := overT G φ hφ
  c := overComposable G φ hφ
  e := overE G φ hφ
  i := overI G φ hφ
  comp_source := sorry
  comp_target := sorry
  identity_source := sorry
  identity_target := sorry
  inverse_source := sorry
  inverse_target := sorry
  associativity := sorry
  right_identity := sorry
  left_identity := sorry
  inverse_comp := sorry
  comp_inverse := sorry

/-- The object space of `G.over φ hφ` is `U` with structure map `φ`. -/
theorem over_U {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) :
    (over G φ hφ).U = Over.mk φ.left := sorry

/-- The arrow space of `G.over φ hφ` is `R` with structure map `t ≫ φ`. -/
theorem over_R {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) :
    (over G φ hφ).R = Over.mk (G.toPreRelation.t.left ≫ φ.left) := sorry

/-- The source map of `G.over φ hφ` has left component `G.s`. -/
theorem over_s {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) :
    (over G φ hφ).s = overS G φ hφ := sorry

/-- The target map of `G.over φ hφ` has left component `G.t`. -/
theorem over_t {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) :
    (over G φ hφ).t = overT G φ hφ := sorry

/-- The composition map of `G.over φ hφ` is the comparison of composable arrows over `X`
followed by `G.c`. -/
theorem over_c {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) :
    (over G φ hφ).c = overComposable G φ hφ := sorry

/-- The identity map of `G.over φ hφ` has left component `G.e`. -/
theorem over_e {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) :
    (over G φ hφ).e = overE G φ hφ := sorry

/-- The inverse map of `G.over φ hφ` has left component `G.i`. -/
theorem over_i {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) :
    (over G φ hφ).i = overI G φ hφ := sorry

/-- Triangle witnessing that the object space of the transported base-changed
groupoid has the same structure morphism as `U' = pullback φ f`. -/
private theorem changeBase_over_UIso_w {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    (PreservesPullback.iso (Over.forget B) φ f).inv ≫ (pullback φ f).hom =
      (changeBase X'.hom (baseChange f.left (over G φ hφ))).U.hom := by
  change (PreservesPullback.iso (Over.forget B) φ f).inv ≫ (pullback φ f).hom =
    pullback.snd φ.left f.left ≫ X'.hom
  rw [← Over.w (pullback.snd φ f)]
  exact PreservesPullback.iso_inv_snd_assoc (Over.forget B) φ f X'.hom

/-- Canonical identification of the object space of
`changeBase X'.hom (baseChange f.left (over G φ hφ))` with `U' = pullback φ f`. -/
def changeBase_over_UIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    (changeBase X'.hom (baseChange f.left (over G φ hφ))).U ≅ pullback φ f :=
  Over.isoMk (PreservesPullback.iso (Over.forget B) φ f).symm
    (by exact changeBase_over_UIso_w G φ hφ f)

/-- Triangle witnessing that the arrow space of the transported base-changed
groupoid has the same structure morphism as `R' = pullback (t ≫ φ) f`. -/
private theorem changeBase_over_RIso_w {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    (PreservesPullback.iso (Over.forget B) (G.toPreRelation.t ≫ φ) f).inv ≫
        (G.toPreRelation.baseChange hφ f).left.hom =
      (changeBase X'.hom (baseChange f.left (over G φ hφ))).R.hom := by
  change (PreservesPullback.iso (Over.forget B) (G.toPreRelation.t ≫ φ) f).inv ≫
      (pullback (G.toPreRelation.t ≫ φ) f).hom =
    pullback.snd (G.toPreRelation.t ≫ φ).left f.left ≫ X'.hom
  rw [← Over.w (pullback.snd (G.toPreRelation.t ≫ φ) f)]
  exact PreservesPullback.iso_inv_snd_assoc (Over.forget B) (G.toPreRelation.t ≫ φ) f X'.hom

/-- Canonical identification of the arrow space of
`changeBase X'.hom (baseChange f.left (over G φ hφ))` with the source of the
invariant base change. -/
def changeBase_over_RIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    (changeBase X'.hom (baseChange f.left (over G φ hφ))).R ≅
      (G.toPreRelation.baseChange hφ f).left :=
  Over.isoMk
    (PreservesPullback.iso (Over.forget B) (G.toPreRelation.t ≫ φ) f).symm
    (by exact changeBase_over_RIso_w G φ hφ f)

/-- Triangle witnessing that `changeBase_over_RIso` identifies the transported
groupoid pre-relation with the invariant base change. -/
private theorem toPreRelation_over_baseChange_w {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    (changeBase_over_RIso G φ hφ f).hom ≫
        (G.toPreRelation.baseChange hφ f).hom =
      ((Over.map
        (prod.map (changeBase_over_UIso G φ hφ f).hom
          (changeBase_over_UIso G φ hφ f).hom)).obj
      (changeBase X'.hom (baseChange f.left (over G φ hφ))).toPreRelation).hom := sorry

/-- The underlying pre-relation of the base change of `G.over` along
`X' ⟶ X`, after transport to `Over B` by `Over.map X'.hom`, is canonically
isomorphic in `Over ((pullback φ f) ⨯ (pullback φ f))` to the invariant base
change of `G.toPreRelation`. -/
def toPreRelation_over_baseChange {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    (Over.map
        (prod.map (changeBase_over_UIso G φ hφ f).hom
          (changeBase_over_UIso G φ hφ f).hom)).obj
      (changeBase X'.hom (baseChange f.left (over G φ hφ))).toPreRelation ≅
      G.toPreRelation.baseChange hφ f :=
  Over.isoMk (changeBase_over_RIso G φ hφ f)
    (by exact toPreRelation_over_baseChange_w G φ hφ f)

/-- The comparison iso identifies defining maps of the two pre-relations. -/
theorem toPreRelation_over_baseChange_hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    (toPreRelation_over_baseChange G φ hφ f).hom.left ≫
        (G.toPreRelation.baseChange hφ f).hom =
      ((Over.map
        (prod.map (changeBase_over_UIso G φ hφ f).hom
          (changeBase_over_UIso G φ hφ f).hom)).obj
      (changeBase X'.hom (baseChange f.left (over G φ hφ))).toPreRelation).hom := sorry

/-- The comparison iso identifies target projections of the two pre-relations. -/
theorem toPreRelation_over_baseChange_t {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    (toPreRelation_over_baseChange G φ hφ f).hom.left ≫
        (G.toPreRelation.baseChange hφ f).t =
      AlgebraicSpace.PreRelation.t ((Over.map
        (prod.map (changeBase_over_UIso G φ hφ f).hom
          (changeBase_over_UIso G φ hφ f).hom)).obj
      (changeBase X'.hom (baseChange f.left (over G φ hφ))).toPreRelation) := sorry

/-- The comparison iso identifies source projections of the two pre-relations. -/
theorem toPreRelation_over_baseChange_s {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    (toPreRelation_over_baseChange G φ hφ f).hom.left ≫
        (G.toPreRelation.baseChange hφ f).s =
      AlgebraicSpace.PreRelation.s ((Over.map
        (prod.map (changeBase_over_UIso G φ hφ f).hom
          (changeBase_over_UIso G φ hφ f).hom)).obj
      (changeBase X'.hom (baseChange f.left (over G φ hφ))).toPreRelation) := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
