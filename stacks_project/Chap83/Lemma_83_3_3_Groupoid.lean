module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import stacks_project.Chap78.Lemma_78_11_2_Groupoid
public import stacks_project.Chap78.Lemma_78_15_1_Action
public import stacks_project.Chap83.Lemma_83_3_3_BaseChange

/-!
# Invariant re-slicing of groupoids and induced actions

An invariant morphism `φ : U ⟶ X` lets a groupoid in algebraic spaces over `B` be regarded
over `X`. Base change of that groupoid along `f.left : X'.left ⟶ X.left` is reconstructed
by fibre products of left components in `AlgebraicSpace S`, then transported to `Over B`
by `Over.map X'.hom`. The underlying pre-relation of the transported groupoid is
canonically isomorphic to the invariant base change of `j`. The same construction on an
action groupoid is the induced `G`-action on `U' = pullback φ f`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open ModObj
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

open AlgebraicSpace

/-- Triangle witnessing that the source map of `G` lies over `X` via `φ`. -/
theorem overS_w {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) :
    G.s.left ≫ φ.left = G.toPreRelation.t.left ≫ φ.left := sorry

/-- Triangle witnessing that the target map of `G` lies over `X` via `φ`. -/
theorem overT_w {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) :
    G.t.left ≫ φ.left = G.toPreRelation.t.left ≫ φ.left := sorry

/-- Triangle witnessing that identity arrows of `G` lie over `X` via `φ`. -/
theorem overE_w {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) :
    G.e.left ≫ G.toPreRelation.t.left ≫ φ.left = φ.left := sorry

/-- Triangle witnessing that inversion of `G` lies over `X` via `φ`. -/
theorem overI_w {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
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
  Over.homMk G.s.left (overS_w G φ hφ)

/-- The target map of `G`, as a morphism over `X`. -/
def overT {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) :
    overR G φ ⟶ overU G φ :=
  Over.homMk G.t.left (overT_w G φ hφ)

/-- The identity-arrow map of `G`, as a morphism over `X`. -/
def overE {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) :
    overU G φ ⟶ overR G φ :=
  Over.homMk G.e.left (overE_w G φ hφ)

/-- The inverse-arrow map of `G`, as a morphism over `X`. -/
def overI {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ) :
    overR G φ ⟶ overR G φ :=
  Over.homMk G.i.left (overI_w G φ hφ)

/-- Triangle witnessing that composition of `G` lies over `X` via `φ`. -/
theorem overComposable_w {S : Scheme.{u}} {B : AlgebraicSpace S}
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
    (overComposable_w G φ hφ)

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

/-- The fibre product `X ×_B B'` of an object of `Over B` along `f : B' ⟶ B`. -/
def baseChangeObj {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (X : Over B) : Over B' :=
  Over.mk (Limits.pullback.snd X.hom f)

/-- The structure morphism of `baseChangeObj f X` is the second projection. -/
theorem baseChangeObj_hom {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (X : Over B) :
    (baseChangeObj f X).hom = Limits.pullback.snd X.hom f := sorry

/-- First projection identity for the fibre-product map induced by a morphism over `B`. -/
theorem baseChangeMap_fst {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    {X Y : Over B} (u : X ⟶ Y) :
    X.hom ≫ 𝟙 B = u.left ≫ Y.hom := sorry

/-- Second projection identity for the fibre-product map induced by a morphism over `B`. -/
theorem baseChangeMap_snd {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    {X Y : Over B} (u : X ⟶ Y) :
    f ≫ 𝟙 B = 𝟙 B' ≫ f := sorry

/-- Triangle witnessing that the fibre-product map of `u` lies over `B'`. -/
theorem baseChangeMap_w {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    {X Y : Over B} (u : X ⟶ Y) :
    Limits.pullback.map X.hom f Y.hom f u.left (𝟙 B') (𝟙 B)
        (baseChangeMap_fst f u) (baseChangeMap_snd f u) ≫
      (baseChangeObj f Y).hom =
    (baseChangeObj f X).hom := sorry

/-- The morphism `X ×_B B' ⟶ Y ×_B B'` induced by `u : X ⟶ Y` over `B`. -/
def baseChangeMap {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    {X Y : Over B} (u : X ⟶ Y) :
    baseChangeObj f X ⟶ baseChangeObj f Y :=
  Over.homMk
    (Limits.pullback.map X.hom f Y.hom f u.left (𝟙 B') (𝟙 B)
      (baseChangeMap_fst f u) (baseChangeMap_snd f u))
    (baseChangeMap_w f u)

/-- Triangle witnessing that the first projection of `X ×_B B'` lies over `B`. -/
theorem baseChangeCounit_w {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (X : Over B) :
    Limits.pullback.fst X.hom f ≫ X.hom =
      ((Over.map f).obj (baseChangeObj f X)).hom := sorry

/-- The canonical projection `(Over.map f).obj (baseChangeObj f X) ⟶ X`. -/
def baseChangeCounit {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (X : Over B) : (Over.map f).obj (baseChangeObj f X) ⟶ X :=
  Over.homMk (Limits.pullback.fst X.hom f) (baseChangeCounit_w f X)

/-- A map of left components over `f` induces a cone over the structure morphism of
`baseChangeObj f X`. -/
theorem baseChangeLift_w {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    {Y : Over B'} {X : Over B} (h : Y.left ⟶ X.left)
    (w : h ≫ X.hom = Y.hom ≫ f) :
    Limits.pullback.lift h Y.hom w ≫ (baseChangeObj f X).hom = Y.hom := sorry

/-- The adjunct `Y ⟶ baseChangeObj f X` of a map of left components lying over `f`. -/
def baseChangeLift {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    {Y : Over B'} {X : Over B} (h : Y.left ⟶ X.left)
    (w : h ≫ X.hom = Y.hom ≫ f) :
    Y ⟶ baseChangeObj f X :=
  Over.homMk (Limits.pullback.lift h Y.hom w) (baseChangeLift_w f h w)

/-- The images of the composable-arrow projections form a cone after fibre-product
base change. -/
theorem baseChangeComposableIso_hom_condition {S : Scheme.{u}}
    {B B' : AlgebraicSpace S} (f : B' ⟶ B) (G : GroupoidAlgebraicSpace B) :
    baseChangeMap f (pullback.fst G.s G.t) ≫ baseChangeMap f G.s =
      baseChangeMap f (pullback.snd G.s G.t) ≫ baseChangeMap f G.t := sorry

/-- The first projection of pulled-back composable arrows, transported to `G.R`
over `B`. -/
def baseChangeComposableIsoInvFst {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (f : B' ⟶ B) (G : GroupoidAlgebraicSpace B) :
    (Over.map f).obj
        (pullback (baseChangeMap f G.s) (baseChangeMap f G.t)) ⟶
      G.R :=
  (Over.map f).map (pullback.fst (baseChangeMap f G.s) (baseChangeMap f G.t)) ≫
    baseChangeCounit f G.R

/-- The second projection of pulled-back composable arrows, transported to `G.R`
over `B`. -/
def baseChangeComposableIsoInvSnd {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (f : B' ⟶ B) (G : GroupoidAlgebraicSpace B) :
    (Over.map f).obj
        (pullback (baseChangeMap f G.s) (baseChangeMap f G.t)) ⟶
      G.R :=
  (Over.map f).map (pullback.snd (baseChangeMap f G.s) (baseChangeMap f G.t)) ≫
    baseChangeCounit f G.R

/-- The transported projections of pulled-back composable arrows form a cone over
`G.s` and `G.t`. -/
theorem baseChangeComposableIso_inv_condition {S : Scheme.{u}}
    {B B' : AlgebraicSpace S} (f : B' ⟶ B) (G : GroupoidAlgebraicSpace B) :
    baseChangeComposableIsoInvFst f G ≫ G.s =
      baseChangeComposableIsoInvSnd f G ≫ G.t := sorry

/-- The adjunct over `B` of pulled-back composable arrows into the original
composable-arrow object. -/
def baseChangeComposableIsoInvOver {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (f : B' ⟶ B) (G : GroupoidAlgebraicSpace B) :
    (Over.map f).obj
        (pullback (baseChangeMap f G.s) (baseChangeMap f G.t)) ⟶
      pullback G.s G.t :=
  pullback.lift (baseChangeComposableIsoInvFst f G)
    (baseChangeComposableIsoInvSnd f G)
    (baseChangeComposableIso_inv_condition f G)

/-- The Stacks comparison `R' ×_{s',U',t'} R' ≅ B' ×_B (R ×_{s,U,t} R)` as an
isomorphism in `Over B'`. -/
def baseChangeComposableIso {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (f : B' ⟶ B) (G : GroupoidAlgebraicSpace B) :
    baseChangeObj f (pullback G.s G.t) ≅
      pullback (baseChangeMap f G.s) (baseChangeMap f G.t) where
  hom :=
    pullback.lift (baseChangeMap f (pullback.fst G.s G.t))
      (baseChangeMap f (pullback.snd G.s G.t))
      (baseChangeComposableIso_hom_condition f G)
  inv :=
    baseChangeLift f (baseChangeComposableIsoInvOver f G).left
      (Over.w (baseChangeComposableIsoInvOver f G))
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The base-changed composition map, transported through the composable-arrow
comparison. -/
def baseChangeComposition {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (f : B' ⟶ B) (G : GroupoidAlgebraicSpace B) :
    pullback (baseChangeMap f G.s) (baseChangeMap f G.t) ⟶
      baseChangeObj f G.R :=
  (baseChangeComposableIso f G).inv ≫ baseChangeMap f G.c

/-- Base change of a groupoid in algebraic spaces along a morphism of bases, using
fibre products of left components. -/
def baseChange {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupoidAlgebraicSpace B) : GroupoidAlgebraicSpace B' where
  U := baseChangeObj f G.U
  R := baseChangeObj f G.R
  s := baseChangeMap f G.s
  t := baseChangeMap f G.t
  e := baseChangeMap f G.e
  i := baseChangeMap f G.i
  c := baseChangeComposition f G
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

/-- The object space of a base-changed groupoid is the fibre product of the original
object space. -/
theorem baseChange_U {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupoidAlgebraicSpace B) :
    (baseChange f G).U = baseChangeObj f G.U := sorry

/-- The arrow space of a base-changed groupoid is the fibre product of the original
arrow space. -/
theorem baseChange_R {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupoidAlgebraicSpace B) :
    (baseChange f G).R = baseChangeObj f G.R := sorry

/-- The source map of a base-changed groupoid is the fibre-product source map. -/
theorem baseChange_s {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupoidAlgebraicSpace B) :
    (baseChange f G).s = baseChangeMap f G.s := sorry

/-- The target map of a base-changed groupoid is the fibre-product target map. -/
theorem baseChange_t {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupoidAlgebraicSpace B) :
    (baseChange f G).t = baseChangeMap f G.t := sorry

/-- The composition of a base-changed groupoid is transported by the composable-arrow
comparison. -/
theorem baseChange_c {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupoidAlgebraicSpace B) :
    (baseChange f G).c = baseChangeComposition f G := sorry

/-- The underlying comparison map for composable arrows lies over the ambient base. -/
theorem changeBaseComposable_condition {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (f : B' ⟶ B) (G : GroupoidAlgebraicSpace B') :
    ((PreservesPullback.iso (Over.forget B) ((Over.map f).map G.s)
          ((Over.map f).map G.t)).hom ≫
        (PreservesPullback.iso (Over.forget B') G.s G.t).inv) ≫
      ((Over.map f).obj (pullback G.s G.t)).hom =
        (pullback ((Over.map f).map G.s) ((Over.map f).map G.t)).hom := sorry

/-- The canonical comparison from composable arrows after changing the ambient base
to the ambient-base image of the original composable-arrow object. -/
def changeBaseComposable {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (f : B' ⟶ B) (G : GroupoidAlgebraicSpace B') :
    pullback ((Over.map f).map G.s) ((Over.map f).map G.t) ⟶
      (Over.map f).obj (pullback G.s G.t) :=
  Over.homMk
    ((PreservesPullback.iso (Over.forget B) ((Over.map f).map G.s)
          ((Over.map f).map G.t)).hom ≫
      (PreservesPullback.iso (Over.forget B') G.s G.t).inv)
    (changeBaseComposable_condition f G)

/-- Regard a groupoid in algebraic spaces over `B'` as a groupoid over `B` along
`f : B' ⟶ B`. -/
def changeBase {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupoidAlgebraicSpace B') : GroupoidAlgebraicSpace B where
  U := (Over.map f).obj G.U
  R := (Over.map f).obj G.R
  s := (Over.map f).map G.s
  t := (Over.map f).map G.t
  e := (Over.map f).map G.e
  i := (Over.map f).map G.i
  c := changeBaseComposable f G ≫ (Over.map f).map G.c
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

/-- The object space of a groupoid regarded over a larger base is the mapped object
space. -/
theorem changeBase_U {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupoidAlgebraicSpace B') :
    (changeBase f G).U = (Over.map f).obj G.U := sorry

/-- The arrow space of a groupoid regarded over a larger base is the mapped arrow
space. -/
theorem changeBase_R {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupoidAlgebraicSpace B') :
    (changeBase f G).R = (Over.map f).obj G.R := sorry

/-- The source map of a groupoid regarded over a larger base is the mapped source
map. -/
theorem changeBase_s {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupoidAlgebraicSpace B') :
    (changeBase f G).s = (Over.map f).map G.s := sorry

/-- The target map of a groupoid regarded over a larger base is the mapped target
map. -/
theorem changeBase_t {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupoidAlgebraicSpace B') :
    (changeBase f G).t = (Over.map f).map G.t := sorry

/-- The composition map over the larger base uses the canonical composable-arrow
comparison. -/
theorem changeBase_c {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupoidAlgebraicSpace B') :
    (changeBase f G).c = changeBaseComposable f G ≫ (Over.map f).map G.c := sorry

/-- The fibre product of `U` with `X'` over `X` is identified with the left
component of `U' = pullback φ f`. -/
def overBaseChangeUIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (φ : U ⟶ X) (f : X' ⟶ X) :
    (Over.forget B).obj (pullback φ f) ≅
      pullback ((Over.forget B).map φ) ((Over.forget B).map f) :=
  PreservesPullback.iso (Over.forget B) φ f

/-- The fibre product of `R` with `X'` over `X` is identified with the left
component of `R' = pullback (t ≫ φ) f`. -/
def overBaseChangeRIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (f : X' ⟶ X) :
    (Over.forget B).obj (pullback (G.toPreRelation.t ≫ φ) f) ≅
      pullback ((Over.forget B).map (G.toPreRelation.t ≫ φ))
        ((Over.forget B).map f) :=
  PreservesPullback.iso (Over.forget B) (G.toPreRelation.t ≫ φ) f

/-- The fibre product `X' ×_X U` of the object space of a groupoid regarded over `X`,
as an algebraic space over `B`. -/
def overBaseChangeU {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (φ : U ⟶ X) (f : X' ⟶ X) : Over B :=
  Over.mk (Limits.pullback.snd ((Over.forget B).map φ) ((Over.forget B).map f) ≫
    X'.hom)

/-- The structure morphism of `overBaseChangeU φ f` is the second projection of
`U ×_X X'` followed by the structure map of `X'`. -/
theorem overBaseChangeU_hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (φ : U ⟶ X) (f : X' ⟶ X) :
    (overBaseChangeU φ f).hom =
      Limits.pullback.snd ((Over.forget B).map φ) ((Over.forget B).map f) ≫
        X'.hom := sorry

/-- The fibre product `X' ×_X R` of the arrow space of a groupoid regarded over `X`,
as an algebraic space over `B`. -/
def overBaseChangeR {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X) (f : X' ⟶ X) :
    Over B :=
  Over.mk (Limits.pullback.snd ((Over.forget B).map (G.toPreRelation.t ≫ φ))
      ((Over.forget B).map f) ≫ X'.hom)

/-- The structure morphism of `overBaseChangeR G φ f` is the second projection of
`R ×_X X'` followed by the structure map of `X'`. -/
theorem overBaseChangeR_hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X) (f : X' ⟶ X) :
    (overBaseChangeR G φ f).hom =
      Limits.pullback.snd ((Over.forget B).map (G.toPreRelation.t ≫ φ))
          ((Over.forget B).map f) ≫ X'.hom := sorry

/-- First projection identity for the induced target map on `R' = X' ×_X R`. -/
theorem overBaseChange_t_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X : Over B} (φ : G.U ⟶ X) :
    (Over.forget B).map (G.toPreRelation.t ≫ φ) ≫ 𝟙 X.left =
      G.t.left ≫ (Over.forget B).map φ := sorry

/-- Second projection identity for the induced target map on `R' = X' ×_X R`. -/
theorem overBaseChange_t_snd {S : Scheme.{u}} {B : AlgebraicSpace S}
    {X X' : Over B} (f : X' ⟶ X) :
    (Over.forget B).map f ≫ 𝟙 X.left = 𝟙 X'.left ≫ (Over.forget B).map f := sorry

/-- The left component of the induced target map of the fibre product groupoid. -/
def overBaseChangeTMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X) (f : X' ⟶ X) :
    Limits.pullback ((Over.forget B).map (G.toPreRelation.t ≫ φ))
        ((Over.forget B).map f) ⟶
      Limits.pullback ((Over.forget B).map φ) ((Over.forget B).map f) :=
  Limits.pullback.map ((Over.forget B).map (G.toPreRelation.t ≫ φ))
    ((Over.forget B).map f) ((Over.forget B).map φ) ((Over.forget B).map f)
    G.t.left (𝟙 X'.left) (𝟙 X.left) (overBaseChange_t_fst G φ)
    (overBaseChange_t_snd f)

/-- Triangle witnessing that the induced target map lies over `B`. -/
theorem overBaseChangeT_w {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X) (f : X' ⟶ X) :
    overBaseChangeTMap G φ f ≫ (overBaseChangeU φ f).hom =
      (overBaseChangeR G φ f).hom := sorry

/-- The target map of the fibre product of `G.over` along `f : X' ⟶ X`. -/
def overBaseChangeT {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X) (f : X' ⟶ X) :
    overBaseChangeR G φ f ⟶ overBaseChangeU φ f :=
  Over.homMk (overBaseChangeTMap G φ f) (overBaseChangeT_w G φ f)

/-- First projection identity for the induced source map on `R' = X' ×_X R`. -/
theorem overBaseChange_s_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) :
    (Over.forget B).map (G.toPreRelation.t ≫ φ) ≫ 𝟙 X.left =
      G.s.left ≫ (Over.forget B).map φ := sorry

/-- The left component of the induced source map of the fibre product groupoid. -/
def overBaseChangeSMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    Limits.pullback ((Over.forget B).map (G.toPreRelation.t ≫ φ))
        ((Over.forget B).map f) ⟶
      Limits.pullback ((Over.forget B).map φ) ((Over.forget B).map f) :=
  Limits.pullback.map ((Over.forget B).map (G.toPreRelation.t ≫ φ))
    ((Over.forget B).map f) ((Over.forget B).map φ) ((Over.forget B).map f)
    G.s.left (𝟙 X'.left) (𝟙 X.left) (overBaseChange_s_fst G φ hφ)
    (overBaseChange_t_snd f)

/-- Triangle witnessing that the induced source map lies over `B`. -/
theorem overBaseChangeS_w {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    overBaseChangeSMap G φ hφ f ≫ (overBaseChangeU φ f).hom =
      (overBaseChangeR G φ f).hom := sorry

/-- The source map of the fibre product of `G.over` along `f : X' ⟶ X`. -/
def overBaseChangeS {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    overBaseChangeR G φ f ⟶ overBaseChangeU φ f :=
  Over.homMk (overBaseChangeSMap G φ hφ f) (overBaseChangeS_w G φ hφ f)

/-- Triangle witnessing that the object space of the transported base-changed
groupoid has the same structure morphism as `U' = pullback φ f`. -/
theorem changeBase_over_UIso_w {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    (PreservesPullback.iso (Over.forget B) φ f).inv ≫ (pullback φ f).hom =
      (changeBase X'.hom (baseChange f.left (over G φ hφ))).U.hom := sorry

/-- Canonical identification of the object space of
`changeBase X'.hom (baseChange f.left (over G φ hφ))` with `U' = pullback φ f`. -/
def changeBase_over_UIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    (changeBase X'.hom (baseChange f.left (over G φ hφ))).U ≅ pullback φ f :=
  Over.isoMk (PreservesPullback.iso (Over.forget B) φ f).symm
    (changeBase_over_UIso_w G φ hφ f)

/-- Triangle witnessing that the arrow space of the transported base-changed
groupoid has the same structure morphism as `R' = pullback (t ≫ φ) f`. -/
theorem changeBase_over_RIso_w {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    (PreservesPullback.iso (Over.forget B) (G.toPreRelation.t ≫ φ) f).inv ≫
        (G.toPreRelation.baseChange hφ f).left.hom =
      (changeBase X'.hom (baseChange f.left (over G φ hφ))).R.hom := sorry

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
    (changeBase_over_RIso_w G φ hφ f)

/-- The underlying pre-relation of
`changeBase X'.hom (baseChange f.left (over G φ hφ))`, transported to a
pre-relation on `U' = pullback φ f`. -/
def toPreRelation_changeBase {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    AlgebraicSpace.PreRelation (pullback φ f) :=
  (Over.map
      (prod.map (changeBase_over_UIso G φ hφ f).hom
        (changeBase_over_UIso G φ hφ f).hom)).obj
    (changeBase X'.hom (baseChange f.left (over G φ hφ))).toPreRelation

/-- Triangle witnessing that `changeBase_over_RIso` identifies the transported
groupoid pre-relation with the invariant base change. -/
theorem toPreRelation_over_baseChange_w {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    (changeBase_over_RIso G φ hφ f).hom ≫
        (G.toPreRelation.baseChange hφ f).hom =
      (toPreRelation_changeBase G φ hφ f).hom := sorry

/-- The underlying pre-relation of the Lemma 78.11.6 base change of `G.over` along
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
    (toPreRelation_over_baseChange_w G φ hφ f)

/-- The comparison iso identifies defining maps of the two pre-relations. -/
theorem toPreRelation_over_baseChange_hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    (toPreRelation_over_baseChange G φ hφ f).hom.left ≫
        (G.toPreRelation.baseChange hφ f).hom =
      (toPreRelation_changeBase G φ hφ f).hom := sorry

/-- The comparison iso identifies target projections of the two pre-relations. -/
theorem toPreRelation_over_baseChange_t {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    (toPreRelation_over_baseChange G φ hφ f).hom.left ≫
        (G.toPreRelation.baseChange hφ f).t =
      (toPreRelation_changeBase G φ hφ f).t := sorry

/-- The comparison iso identifies source projections of the two pre-relations. -/
theorem toPreRelation_over_baseChange_s {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X X' : Over B} (φ : G.U ⟶ X)
    (hφ : G.toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    (toPreRelation_over_baseChange G φ hφ f).hom.left ≫
        (G.toPreRelation.baseChange hφ f).s =
      (toPreRelation_changeBase G φ hφ f).s := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace

namespace AlgebraicGeometry.GroupAlgebraicSpace.Action

open AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The two projections of the induced action on `U' = pullback φ f` form a cone over
`φ` and `f`. -/
theorem smulPullback_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (Xg : Action G) {X X' : Over B} (φ : Xg.X ⟶ X)
    (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    ((G.X ◁ Limits.pullback.fst φ f) ≫ γ[G.X, Xg.X]) ≫ φ =
      (snd G.X (Limits.pullback φ f) ≫ Limits.pullback.snd φ f) ≫ f := sorry

/-- The action map of the induced `G`-action on `U' = pullback φ f`. -/
def smulPullback {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (Xg : Action G) {X X' : Over B} (φ : Xg.X ⟶ X)
    (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    G.X ⊗ Limits.pullback φ f ⟶ Limits.pullback φ f :=
  Limits.pullback.lift ((G.X ◁ Limits.pullback.fst φ f) ≫ γ[G.X, Xg.X])
    (snd G.X (Limits.pullback φ f) ≫ Limits.pullback.snd φ f)
    (smulPullback_condition G Xg φ hφ f)

/-- The induced `G`-action on `U' = pullback φ f` along an invariant morphism `φ`. -/
def pullback {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (Xg : Action G) {X X' : Over B} (φ : Xg.X ⟶ X)
    (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    Action G where
  X := Limits.pullback φ f
  mod :=
    { smul := smulPullback G Xg φ hφ f
      one_smul := sorry
      mul_smul := sorry }

/-- The underlying object of the induced action is `U' = pullback φ f`. -/
theorem pullback_X {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (Xg : Action G) {X X' : Over B} (φ : Xg.X ⟶ X)
    (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    (pullback G Xg φ hφ f).X = Limits.pullback φ f := sorry

/-- The action map of the induced action is `smulPullback`. -/
theorem pullback_smul {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (Xg : Action G) {X X' : Over B} (φ : Xg.X ⟶ X)
    (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ) (f : X' ⟶ X) :
    γ[G.X, (pullback G Xg φ hφ f).X] = smulPullback G Xg φ hφ f := sorry

end AlgebraicGeometry.GroupAlgebraicSpace.Action

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Invariance makes `(g, u') ↦ (g, u)` a cone over `t ≫ φ` and `f`. -/
theorem actionPullbackArrowHom_w {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (Xg : GroupAlgebraicSpace.Action G) {X X' : Over B}
    (φ : Xg.X ⟶ X) (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (G.X ◁ Limits.pullback.fst φ f) ≫ ((ofAction G Xg).toPreRelation.t ≫ φ) =
      (snd G.X (Limits.pullback φ f) ≫ Limits.pullback.snd φ f) ≫ f := sorry

/-- The canonical map `G.X ⊗ pullback φ f ⟶ pullback (t ≫ φ) f` induced by
invariance. -/
def actionPullbackArrowHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (Xg : GroupAlgebraicSpace.Action G) {X X' : Over B}
    (φ : Xg.X ⟶ X) (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ)
    (f : X' ⟶ X) :
    G.X ⊗ Limits.pullback φ f ⟶
      pullback ((ofAction G Xg).toPreRelation.t ≫ φ) f :=
  Limits.pullback.lift (G.X ◁ Limits.pullback.fst φ f)
    (snd G.X (Limits.pullback φ f) ≫ Limits.pullback.snd φ f)
    (actionPullbackArrowHom_w G Xg φ hφ f)

/-- The pair `(g, u)` and the `X'`-coordinate of `X' ×_X (G ⊗ U)` form a cone over
`φ` and `f`. -/
theorem actionPullbackArrowInv_w {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (Xg : GroupAlgebraicSpace.Action G) {X X' : Over B}
    (φ : Xg.X ⟶ X) (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (Limits.pullback.fst ((ofAction G Xg).toPreRelation.t ≫ φ) f ≫
        snd G.X Xg.X) ≫ φ =
      Limits.pullback.snd ((ofAction G Xg).toPreRelation.t ≫ φ) f ≫ f := sorry

/-- Inverse of `actionPullbackArrowHom`, pairing the group coordinate with the
induced point of `U'`. -/
def actionPullbackArrowInv {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (Xg : GroupAlgebraicSpace.Action G) {X X' : Over B}
    (φ : Xg.X ⟶ X) (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ)
    (f : X' ⟶ X) :
    pullback ((ofAction G Xg).toPreRelation.t ≫ φ) f ⟶
      G.X ⊗ Limits.pullback φ f :=
  CartesianMonoidalCategory.lift
    (Limits.pullback.fst ((ofAction G Xg).toPreRelation.t ≫ φ) f ≫ fst G.X Xg.X)
    (Limits.pullback.lift
      (Limits.pullback.fst ((ofAction G Xg).toPreRelation.t ≫ φ) f ≫ snd G.X Xg.X)
      (Limits.pullback.snd ((ofAction G Xg).toPreRelation.t ≫ φ) f)
      (actionPullbackArrowInv_w G Xg φ hφ f))

/-- Canonical isomorphism `G.X ⊗ U' ≅ X' ×_X (G ⊗ U)` induced by invariance of
`φ`, as an identification of chosen fibre products in `Over B`. -/
def actionPullbackArrowIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (Xg : GroupAlgebraicSpace.Action G) {X X' : Over B}
    (φ : Xg.X ⟶ X) (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ)
    (f : X' ⟶ X) :
    G.X ⊗ Limits.pullback φ f ≅
      pullback ((ofAction G Xg).toPreRelation.t ≫ φ) f :=
  { hom := actionPullbackArrowHom G Xg φ hφ f
    inv := actionPullbackArrowInv G Xg φ hφ f
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- Triangle witnessing that `actionPullbackArrowIso` identifies the induced-action
pre-relation with the invariant base change. -/
theorem toPreRelation_pullback_w {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (Xg : GroupAlgebraicSpace.Action G) {X X' : Over B}
    (φ : Xg.X ⟶ X) (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (actionPullbackArrowIso G Xg φ hφ f).hom ≫
        ((ofAction G Xg).toPreRelation.baseChange hφ f).hom =
      (ofAction G
        (GroupAlgebraicSpace.Action.pullback G Xg φ hφ f)).toPreRelation.hom := sorry

/-- The underlying pre-relation of the induced `G`-action on `U'` is canonically
isomorphic to the invariant base change of the original action groupoid. -/
def toPreRelation_pullback {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (Xg : GroupAlgebraicSpace.Action G) {X X' : Over B}
    (φ : Xg.X ⟶ X) (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (ofAction G
        (GroupAlgebraicSpace.Action.pullback G Xg φ hφ f)).toPreRelation ≅
      (ofAction G Xg).toPreRelation.baseChange hφ f :=
  Over.isoMk (actionPullbackArrowIso G Xg φ hφ f)
    (toPreRelation_pullback_w G Xg φ hφ f)

/-- The action comparison identifies defining maps of the two pre-relations. -/
theorem toPreRelation_pullback_hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (Xg : GroupAlgebraicSpace.Action G) {X X' : Over B}
    (φ : Xg.X ⟶ X) (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (toPreRelation_pullback G Xg φ hφ f).hom.left ≫
        ((ofAction G Xg).toPreRelation.baseChange hφ f).hom =
      (ofAction G
        (GroupAlgebraicSpace.Action.pullback G Xg φ hφ f)).toPreRelation.hom := sorry

/-- The action comparison identifies target projections of the two pre-relations. -/
theorem toPreRelation_pullback_t {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (Xg : GroupAlgebraicSpace.Action G) {X X' : Over B}
    (φ : Xg.X ⟶ X) (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (toPreRelation_pullback G Xg φ hφ f).hom.left ≫
        ((ofAction G Xg).toPreRelation.baseChange hφ f).t =
      (ofAction G
        (GroupAlgebraicSpace.Action.pullback G Xg φ hφ f)).toPreRelation.t := sorry

/-- The action comparison identifies source projections of the two pre-relations. -/
theorem toPreRelation_pullback_s {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (Xg : GroupAlgebraicSpace.Action G) {X X' : Over B}
    (φ : Xg.X ⟶ X) (hφ : (ofAction G Xg).toPreRelation.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (toPreRelation_pullback G Xg φ hφ f).hom.left ≫
        ((ofAction G Xg).toPreRelation.baseChange hφ f).s =
      (ofAction G
        (GroupAlgebraicSpace.Action.pullback G Xg φ hφ f)).toPreRelation.s := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
