/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Composition
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Fiber
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Reindex.MapIso.Basic
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Coherence
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import ReasLib.CategoryTheory.Fibered.StronglyCartesian.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StackInSets.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Isom

/-!
# Explicit `[U/R]`-descent data

A descent datum consists of maps into the object and arrow spaces of a groupoid, satisfying
endpoint and cocycle equations. Such data and their morphisms admit explicit refinement
operations and describe objects and morphisms of the fppf quotient stack.
-/

@[expose] public section

-- Exposed constructions reference private proposition-valued laws for their explicit components.
set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits Opposite
open Functor
open CategoryTheory.CategoryOfElements

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The member `T_i` of an indexed family over `T`, viewed as a scheme over `S`. -/
def coverOver {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i : ι) :
    Over S :=
  Over.mk ((family i).hom ≫ T.hom)

/-- The structure morphism `T_i ⟶ T` of a covering member. -/
def coverHom {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i : ι) :
    coverOver family i ⟶ T :=
  Over.homMk (family i).hom rfl

/-- `coverHom family i` is the over-morphism induced by `(family i).hom`. -/
theorem coverOver_hom {S : Scheme.{u}} {T : Over S} {ι : Type u}
    (family : ι → Over T.left) (i : ι) :
    coverHom family i = Over.homMk (family i).hom rfl :=
  rfl

/-- The fibre product `T_i ×_T T_j`, viewed as a scheme over `S`. -/
def pairOver {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i j : ι) :
    Over S :=
  Over.mk (pullback.fst (family i).hom (family j).hom ≫ (family i).hom ≫ T.hom)

/-- The projection `pr₀ : T_i ×_T T_j ⟶ T_i`. -/
def pr0 {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i j : ι) :
    pairOver family i j ⟶ coverOver family i :=
  Over.homMk (pullback.fst (family i).hom (family j).hom) rfl

/-- Compatibility of `pr1` with the structure morphisms to `S`. -/
theorem pr1_w {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i j : ι) :
    pullback.snd (family i).hom (family j).hom ≫ (coverOver family j).hom =
      (pairOver family i j).hom :=
  sorry

/-- The projection `pr₁ : T_i ×_T T_j ⟶ T_j`. -/
def pr1 {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i j : ι) :
    pairOver family i j ⟶ coverOver family j :=
  Over.homMk (pullback.snd (family i).hom (family j).hom) (pr1_w family i j)

/-- `pr0` is induced by `pullback.fst`. -/
theorem pairOver_pr0 {S : Scheme.{u}} {T : Over S} {ι : Type u}
    (family : ι → Over T.left) (i j : ι) :
    pr0 family i j = Over.homMk (pullback.fst (family i).hom (family j).hom) rfl :=
  rfl

/-- `pr1` is induced by `pullback.snd`. -/
theorem pairOver_pr1 {S : Scheme.{u}} {T : Over S} {ι : Type u}
    (family : ι → Over T.left) (i j : ι) :
    pr1 family i j =
      Over.homMk (pullback.snd (family i).hom (family j).hom) (pr1_w family i j) :=
  rfl

/-- The two projections of `T_i ×_T T_j` agree after composing to `T`. -/
theorem pr0_coverHom {S : Scheme.{u}} {T : Over S} {ι : Type u}
    (family : ι → Over T.left) (i j : ι) :
    pr0 family i j ≫ coverHom family i = pr1 family i j ≫ coverHom family j :=
  sorry

/-- The triple fibre product `T_i ×_T T_j ×_T T_k`, as `(T_i ×_T T_j) ×_T T_k` over `S`. -/
def tripleOver {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (i j k : ι) : Over S :=
  Over.mk
    (pullback.fst (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
        (family k).hom ≫
      (pairOver family i j).hom)

/-- The projection `pr₀₁ : T_i ×_T T_j ×_T T_k ⟶ T_i ×_T T_j`. -/
def pr01 {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i j k : ι) :
    tripleOver family i j k ⟶ pairOver family i j :=
  Over.homMk
    (pullback.fst (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
      (family k).hom)
    rfl

/-- The two legs of `pr12Scheme` agree over `T`. -/
theorem pr12Scheme_w {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (i j k : ι) :
    (pullback.fst (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
          (family k).hom ≫
        pullback.snd (family i).hom (family j).hom) ≫
        (family j).hom =
      pullback.snd (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
          (family k).hom ≫
        (family k).hom :=
  sorry

/-- Underlying scheme map of `pr₁₂`. -/
def pr12Scheme {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (i j k : ι) : (tripleOver family i j k).left ⟶ (pairOver family j k).left :=
  pullback.lift
    (pullback.fst (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
        (family k).hom ≫
      pullback.snd (family i).hom (family j).hom)
    (pullback.snd (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
      (family k).hom)
    (pr12Scheme_w family i j k)

/-- `pr12Scheme` lies over `S`. -/
theorem pr12_w {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (i j k : ι) :
    pr12Scheme family i j k ≫ (pairOver family j k).hom = (tripleOver family i j k).hom :=
  sorry

/-- The projection `pr₁₂ : T_i ×_T T_j ×_T T_k ⟶ T_j ×_T T_k`. -/
def pr12 {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i j k : ι) :
    tripleOver family i j k ⟶ pairOver family j k :=
  Over.homMk (pr12Scheme family i j k) (pr12_w family i j k)

/-- The two legs of `pr02Scheme` agree over `T`. -/
theorem pr02Scheme_w {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (i j k : ι) :
    (pullback.fst (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
          (family k).hom ≫
        pullback.fst (family i).hom (family j).hom) ≫
        (family i).hom =
      pullback.snd (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
          (family k).hom ≫
        (family k).hom :=
  sorry

/-- Underlying scheme map of `pr₀₂`. -/
def pr02Scheme {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (i j k : ι) : (tripleOver family i j k).left ⟶ (pairOver family i k).left :=
  pullback.lift
    (pullback.fst (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
        (family k).hom ≫
      pullback.fst (family i).hom (family j).hom)
    (pullback.snd (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
      (family k).hom)
    (pr02Scheme_w family i j k)

/-- `pr02Scheme` lies over `S`. -/
theorem pr02_w {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (i j k : ι) :
    pr02Scheme family i j k ≫ (pairOver family i k).hom = (tripleOver family i j k).hom :=
  sorry

/-- The projection `pr₀₂ : T_i ×_T T_j ×_T T_k ⟶ T_i ×_T T_k`. -/
def pr02 {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i j k : ι) :
    tripleOver family i j k ⟶ pairOver family i k :=
  Over.homMk (pr02Scheme family i j k) (pr02_w family i j k)

/-- Compose two `X`-valued arrows of `G` by transporting the fibre product of `s` and `t`
along `Over.forget B` and applying `G.c`. Later/earlier is `pullback.fst`/`pullback.snd`. -/
def compArrows {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : AlgebraicSpace S} (later earlier : X ⟶ G.R.left)
    (h : later ≫ G.s.left = earlier ≫ G.t.left) : X ⟶ G.R.left :=
  pullback.lift later earlier h ≫
    (PreservesPullback.iso (Over.forget B) G.s G.t).inv ≫ G.c.left

/-- `compArrows` is the composite of the forgetful pullback comparison with `G.c.left`. -/
theorem compArrows_eq {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : AlgebraicSpace S} (later earlier : X ⟶ G.R.left)
    (h : later ≫ G.s.left = earlier ≫ G.t.left) :
    G.compArrows later earlier h =
      pullback.lift later earlier h ≫
        (PreservesPullback.iso (Over.forget B) G.s G.t).inv ≫ G.c.left :=
  rfl

/-- The object `π(u)` of `[U/R]_T` associated to a morphism `u : T ⟶ U`. -/
def atlasObj {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (u : ofOver T ⟶ G.U.left) : (fppfQuotientStack G).p.Fiber T :=
  ((fppfAtlas G).fiberFunctor T).obj (objOfHom u)

/-- `atlasObj G u` is the image of `objOfHom u` under the fibre functor of `fppfAtlas G`. -/
theorem atlasObj_eq {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (u : ofOver T ⟶ G.U.left) :
    atlasObj G u = ((fppfAtlas G).fiberFunctor T).obj (objOfHom u) :=
  rfl

/-- The fibre morphism `π(r) : π(s ∘ r) ⟶ π(t ∘ r)` associated to `r : T ⟶ R`. -/
def atlasArrow {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (r : ofOver T ⟶ G.R.left) :
    ((atlasSource G).fiberFunctor T).obj (objOfHom r) ⟶
      ((atlasTarget G).fiberFunctor T).obj (objOfHom r) :=
  (CartesianBasedFunctor.fiberNatTrans (sourceTarget G) T).app (objOfHom r)

/-- `atlasArrow G r` is the fibre component of `sourceTarget G` at `objOfHom r`. -/
theorem atlasArrow_eq {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (r : ofOver T ⟶ G.R.left) :
    atlasArrow G r =
      (CartesianBasedFunctor.fiberNatTrans (sourceTarget G) T).app (objOfHom r) :=
  rfl

/-- The canonical identification `π(u ∘ f) ≅ f^* π(u)`. -/
def atlasObjReindexIso {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T T' : Over S} (f : T' ⟶ T) (u : ofOver T ⟶ G.U.left) :
    atlasObj G (ofOverMap f ≫ u) ≅ Chosen.reindexObj (fppfQuotientStack G).p f (atlasObj G u) :=
  ((fppfAtlas G).fiberFunctor T').mapIso (objOfHomReindexIso f u) ≪≫
    (CartesianBasedFunctor.Reindex.mapIso (fppfAtlas G) (Cleavage.ofIsFibered (stackInSets G.U.left).p) (Cleavage.ofIsFibered (fppfQuotientStack G).p) f (objOfHom u)).symm

/-- The point-reindexing comparison factors through the atlas fibre functor and its cartesian comparison. -/
theorem atlasObjReindexIso_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T T' : Over S} (f : T' ⟶ T)
    (u : ofOver T ⟶ G.U.left) :
    atlasObjReindexIso G f u =
      ((fppfAtlas G).fiberFunctor T').mapIso (objOfHomReindexIso f u) ≪≫
        (CartesianBasedFunctor.Reindex.mapIso (fppfAtlas G) (Cleavage.ofIsFibered (stackInSets G.U.left).p) (Cleavage.ofIsFibered (fppfQuotientStack G).p) f (objOfHom u)).symm :=
  rfl

/-- The identity comparison between the composite fibre functors is vertical. -/
private theorem atlasSourceFiberIso_over {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} (r : ofOver T ⟶ G.R.left) :
    (fppfQuotientStack G).p.IsHomLift (𝟙 T)
      (Iso.refl (((atlasSource G).fiberFunctor T).obj (objOfHom r)).1).hom := sorry

/-- Forget `π ∘ s` to `π` on the fibre object associated to `r`. -/
def atlasSourceFiberIso {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (r : ofOver T ⟶ G.R.left) :
    ((atlasSource G).fiberFunctor T).obj (objOfHom r) ≅
      ((fppfAtlas G).fiberFunctor T).obj
        (((stackInSets.map G.s.left).fiberFunctor T).obj (objOfHom r)) :=
  Fiber.isoMk (Iso.refl _) (atlasSourceFiberIso_over G r)

/-- The identity comparison between the composite fibre functors is vertical. -/
private theorem atlasTargetFiberIso_over {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} (r : ofOver T ⟶ G.R.left) :
    (fppfQuotientStack G).p.IsHomLift (𝟙 T)
      (Iso.refl (((atlasTarget G).fiberFunctor T).obj (objOfHom r)).1).hom := sorry

/-- Forget `π ∘ t` to `π` on the fibre object associated to `r`. -/
def atlasTargetFiberIso {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (r : ofOver T ⟶ G.R.left) :
    ((atlasTarget G).fiberFunctor T).obj (objOfHom r) ≅
      ((fppfAtlas G).fiberFunctor T).obj
        (((stackInSets.map G.t.left).fiberFunctor T).obj (objOfHom r)) :=
  Fiber.isoMk (Iso.refl _) (atlasTargetFiberIso_over G r)

/-- The canonical associator `pr₀^* f_i^* x ≅ pr₁^* f_j^* x`. -/
def overlapAssociator {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (x : (fppfQuotientStack G).p.Fiber T) (i j : ι) :
    Chosen.reindexObj (fppfQuotientStack G).p (pr0 family i j) (Chosen.reindexObj (fppfQuotientStack G).p (coverHom family i) x) ≅
      Chosen.reindexObj (fppfQuotientStack G).p (pr1 family i j) (Chosen.reindexObj (fppfQuotientStack G).p (coverHom family j) x) :=
  (Chosen.Reindex.specifiedCompIsoApp (fppfQuotientStack G).p
      (coverHom family i) (pr0 family i j)
      (pr0 family i j ≫ coverHom family i) rfl x).symm ≪≫
    Chosen.Reindex.congrIsoApp (fppfQuotientStack G).p (pr0_coverHom family i j) x ≪≫
    Chosen.Reindex.specifiedCompIsoApp (fppfQuotientStack G).p
      (coverHom family j) (pr1 family i j)
      (pr1 family i j ≫ coverHom family j) rfl x

/-- `overlapAssociator` is the selected-cleavage composite comparison on `pr₀` and `pr₁`. -/
theorem overlapAssociator_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} {ι : Type u}
    (family : ι → Over T.left) (x : (fppfQuotientStack G).p.Fiber T) (i j : ι) :
    overlapAssociator G family x i j =
      (Chosen.Reindex.specifiedCompIsoApp (fppfQuotientStack G).p
          (coverHom family i) (pr0 family i j)
          (pr0 family i j ≫ coverHom family i) rfl x).symm ≪≫
        Chosen.Reindex.congrIsoApp (fppfQuotientStack G).p (pr0_coverHom family i j) x ≪≫
        Chosen.Reindex.specifiedCompIsoApp (fppfQuotientStack G).p
          (coverHom family j) (pr1 family i j)
          (pr1 family i j ≫ coverHom family j) rfl x :=
  rfl

/-- The canonical source comparison `π(s ∘ r) ≅ pr₀^* π(u)` from the source law. -/
def sourceComparison {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} {ι : Type u} (family : ι → Over T.left) {i j : ι}
    (u : ofOver (coverOver family i) ⟶ G.U.left)
    {r : ofOver (pairOver family i j) ⟶ G.R.left}
    (hs : r ≫ G.s.left = ofOverMap (pr0 family i j) ≫ u) :
    ((atlasSource G).fiberFunctor (pairOver family i j)).obj (objOfHom r) ≅
      Chosen.reindexObj (fppfQuotientStack G).p (pr0 family i j) (atlasObj G u) :=
  atlasSourceFiberIso G r ≪≫
    ((fppfAtlas G).fiberFunctor (pairOver family i j)).mapIso
      (objOfHomMapIso G.s.left r ≪≫
        eqToIso (congrArg objOfHom hs) ≪≫ objOfHomReindexIso (pr0 family i j) u) ≪≫
    (CartesianBasedFunctor.Reindex.mapIso (fppfAtlas G) (Cleavage.ofIsFibered (stackInSets G.U.left).p) (Cleavage.ofIsFibered (fppfQuotientStack G).p) (pr0 family i j) (objOfHom u)).symm

/-- `sourceComparison` is the composite of `atlasSourceFiberIso`, `objOfHomMapIso`, and
`atlasObjReindexIso`. -/
theorem sourceComparison_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} {ι : Type u}
    (family : ι → Over T.left) {i j : ι}
    (u : ofOver (coverOver family i) ⟶ G.U.left)
    {r : ofOver (pairOver family i j) ⟶ G.R.left}
    (hs : r ≫ G.s.left = ofOverMap (pr0 family i j) ≫ u) :
    sourceComparison G family u hs =
      atlasSourceFiberIso G r ≪≫
        ((fppfAtlas G).fiberFunctor (pairOver family i j)).mapIso
          (objOfHomMapIso G.s.left r ≪≫
            eqToIso (congrArg objOfHom hs) ≪≫ objOfHomReindexIso (pr0 family i j) u) ≪≫
        (CartesianBasedFunctor.Reindex.mapIso (fppfAtlas G) (Cleavage.ofIsFibered (stackInSets G.U.left).p) (Cleavage.ofIsFibered (fppfQuotientStack G).p) (pr0 family i j) (objOfHom u)).symm :=
  rfl

/-- The canonical target comparison `π(t ∘ r) ≅ pr₁^* π(u)` from the target law. -/
def targetComparison {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} {ι : Type u} (family : ι → Over T.left) {i j : ι}
    (u : ofOver (coverOver family j) ⟶ G.U.left)
    {r : ofOver (pairOver family i j) ⟶ G.R.left}
    (ht : r ≫ G.t.left = ofOverMap (pr1 family i j) ≫ u) :
    ((atlasTarget G).fiberFunctor (pairOver family i j)).obj (objOfHom r) ≅
      Chosen.reindexObj (fppfQuotientStack G).p (pr1 family i j) (atlasObj G u) :=
  atlasTargetFiberIso G r ≪≫
    ((fppfAtlas G).fiberFunctor (pairOver family i j)).mapIso
      (objOfHomMapIso G.t.left r ≪≫
        eqToIso (congrArg objOfHom ht) ≪≫ objOfHomReindexIso (pr1 family i j) u) ≪≫
    (CartesianBasedFunctor.Reindex.mapIso (fppfAtlas G) (Cleavage.ofIsFibered (stackInSets G.U.left).p) (Cleavage.ofIsFibered (fppfQuotientStack G).p) (pr1 family i j) (objOfHom u)).symm

/-- `targetComparison` is the composite of `atlasTargetFiberIso`, `objOfHomMapIso`, and
`atlasObjReindexIso`. -/
theorem targetComparison_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} {ι : Type u}
    (family : ι → Over T.left) {i j : ι}
    (u : ofOver (coverOver family j) ⟶ G.U.left)
    {r : ofOver (pairOver family i j) ⟶ G.R.left}
    (ht : r ≫ G.t.left = ofOverMap (pr1 family i j) ≫ u) :
    targetComparison G family u ht =
      atlasTargetFiberIso G r ≪≫
        ((fppfAtlas G).fiberFunctor (pairOver family i j)).mapIso
          (objOfHomMapIso G.t.left r ≪≫
            eqToIso (congrArg objOfHom ht) ≪≫ objOfHomReindexIso (pr1 family i j) u) ≪≫
        (CartesianBasedFunctor.Reindex.mapIso (fppfAtlas G) (Cleavage.ofIsFibered (stackInSets G.U.left).p) (Cleavage.ofIsFibered (fppfQuotientStack G).p) (pr1 family i j) (objOfHom u)).symm :=
  rfl

/-- The canonical comparison `π(s ∘ r) ≅ π(u)` on a covering member from `u = s ∘ r`. -/
def sourceHomComparison {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (u : ofOver T ⟶ G.U.left) (rR : ofOver T ⟶ G.R.left)
    (hs : u = rR ≫ G.s.left) :
    ((atlasSource G).fiberFunctor T).obj (objOfHom rR) ≅ atlasObj G u :=
  atlasSourceFiberIso G rR ≪≫
    ((fppfAtlas G).fiberFunctor T).mapIso
      (objOfHomMapIso G.s.left rR ≪≫ eqToIso (congrArg objOfHom hs.symm))

/-- `sourceHomComparison` is the composite of `atlasSourceFiberIso` and `objOfHomMapIso`. -/
theorem sourceHomComparison_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S}
    (u : ofOver T ⟶ G.U.left) (rR : ofOver T ⟶ G.R.left)
    (hs : u = rR ≫ G.s.left) :
    sourceHomComparison G u rR hs =
      atlasSourceFiberIso G rR ≪≫
        ((fppfAtlas G).fiberFunctor T).mapIso
          (objOfHomMapIso G.s.left rR ≪≫ eqToIso (congrArg objOfHom hs.symm)) :=
  rfl

/-- The canonical comparison `π(t ∘ r) ≅ π(u)` on a covering member from `u = t ∘ r`. -/
def targetHomComparison {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (u : ofOver T ⟶ G.U.left) (rR : ofOver T ⟶ G.R.left)
    (ht : u = rR ≫ G.t.left) :
    ((atlasTarget G).fiberFunctor T).obj (objOfHom rR) ≅ atlasObj G u :=
  atlasTargetFiberIso G rR ≪≫
    ((fppfAtlas G).fiberFunctor T).mapIso
      (objOfHomMapIso G.t.left rR ≪≫ eqToIso (congrArg objOfHom ht.symm))

/-- `targetHomComparison` is the composite of `atlasTargetFiberIso` and `objOfHomMapIso`. -/
theorem targetHomComparison_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S}
    (u : ofOver T ⟶ G.U.left) (rR : ofOver T ⟶ G.R.left)
    (ht : u = rR ≫ G.t.left) :
    targetHomComparison G u rR ht =
      atlasTargetFiberIso G rR ≪≫
        ((fppfAtlas G).fiberFunctor T).mapIso
          (objOfHomMapIso G.t.left rR ≪≫ eqToIso (congrArg objOfHom ht.symm)) :=
  rfl

/-- A `[U/R]`-descent datum relative to an indexed family of schemes over `T`. -/
structure DescentDatum {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} {ι : Type u} (family : ι → Over T.left) where
  /-- The object maps `u_i : T_i ⟶ U`. -/
  u : ∀ i, ofOver (coverOver family i) ⟶ G.U.left
  /-- The arrow maps `r_ij : T_i ×_T T_j ⟶ R`. -/
  r : ∀ i j, ofOver (pairOver family i j) ⟶ G.R.left
  /-- Source law: `s ∘ r_ij = u_i ∘ pr₀`. -/
  source : ∀ i j, r i j ≫ G.s.left = ofOverMap (pr0 family i j) ≫ u i
  /-- Target law: `t ∘ r_ij = u_j ∘ pr₁`. -/
  target : ∀ i j, r i j ≫ G.t.left = ofOverMap (pr1 family i j) ≫ u j
  /-- Cocycle law: `c ∘ (r_jk ∘ pr₁₂, r_ij ∘ pr₀₁) = r_ik ∘ pr₀₂`. -/
  cocycle :
    ∀ i j k
      (h :
        (ofOverMap (pr12 family i j k) ≫ r j k) ≫ G.s.left =
          (ofOverMap (pr01 family i j k) ≫ r i j) ≫ G.t.left),
      G.compArrows (ofOverMap (pr12 family i j k) ≫ r j k)
          (ofOverMap (pr01 family i j k) ≫ r i j) h =
        ofOverMap (pr02 family i j k) ≫ r i k

namespace DescentDatum

/-- Source, target, and cocycle laws of a descent datum. -/
theorem spec {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left} (D : DescentDatum G family) :
    (∀ i j, D.r i j ≫ G.s.left = ofOverMap (pr0 family i j) ≫ D.u i) ∧
      (∀ i j, D.r i j ≫ G.t.left = ofOverMap (pr1 family i j) ≫ D.u j) ∧
        ∀ i j k
          (h :
            (ofOverMap (pr12 family i j k) ≫ D.r j k) ≫ G.s.left =
              (ofOverMap (pr01 family i j k) ≫ D.r i j) ≫ G.t.left),
          G.compArrows (ofOverMap (pr12 family i j k) ≫ D.r j k)
              (ofOverMap (pr01 family i j k) ≫ D.r i j) h =
            ofOverMap (pr02 family i j k) ≫ D.r i k :=
  ⟨D.source, D.target, D.cocycle⟩

/-- The identity covering `{T ⟶ T}` as a `PUnit`-indexed family. -/
def identityFamily {S : Scheme.{u}} (T : Over S) : PUnit.{u + 1} → Over T.left :=
  fun _ ↦ Over.mk (𝟙 T.left)

/-- The identity covering member is `T` over `S`. -/
def identityCoverHom {S : Scheme.{u}} (T : Over S) :
    coverOver (identityFamily T) PUnit.unit ⟶ T :=
  Over.homMk (𝟙 T.left) rfl

/-- The pair of the identity covering maps to `T` by `pr₀`. -/
def identityPairHom {S : Scheme.{u}} (T : Over S) :
    pairOver (identityFamily T) PUnit.unit PUnit.unit ⟶ T :=
  Over.homMk (pullback.fst (𝟙 T.left) (𝟙 T.left) ≫ 𝟙 T.left) rfl

/-- The prescribed component maps satisfy the endpoint and cocycle equations. -/
private theorem trivial_laws {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (u : ofOver T ⟶ G.U.left) :
    let objectMaps : ∀ i, ofOver (coverOver (identityFamily T) i) ⟶ G.U.left := fun _ ↦ ofOverMap (identityCoverHom T) ≫ u
    let r : ∀ i j, ofOver (pairOver (identityFamily T) i j) ⟶ G.R.left := fun _ _ ↦ ofOverMap (identityPairHom T) ≫ u ≫ G.e.left
    (∀ i j, r i j ≫ G.s.left = ofOverMap (pr0 (identityFamily T) i j) ≫ objectMaps i) ∧
      (∀ i j, r i j ≫ G.t.left = ofOverMap (pr1 (identityFamily T) i j) ≫ objectMaps j) ∧
        ∀ i j k
          (h :
            (ofOverMap (pr12 (identityFamily T) i j k) ≫ r j k) ≫ G.s.left =
              (ofOverMap (pr01 (identityFamily T) i j k) ≫ r i j) ≫ G.t.left),
          G.compArrows (ofOverMap (pr12 (identityFamily T) i j k) ≫ r j k)
              (ofOverMap (pr01 (identityFamily T) i j k) ≫ r i j) h =
            ofOverMap (pr02 (identityFamily T) i j k) ≫ r i k := sorry

/-- The trivial descent datum of a morphism `T ⟶ U` on the identity covering. -/
def trivial {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (u : ofOver T ⟶ G.U.left) :
    DescentDatum G (identityFamily T) where
  u := fun _ ↦ ofOverMap (identityCoverHom T) ≫ u
  r := fun _ _ ↦ ofOverMap (identityPairHom T) ≫ u ≫ G.e.left
  source := (trivial_laws G u).1
  target := (trivial_laws G u).2.1
  cocycle := (trivial_laws G u).2.2

/-- The object map of `trivial G u` is `u` after identifying the identity covering with `T`. -/
theorem trivial_u {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (u : ofOver T ⟶ G.U.left) :
    (trivial G u).u PUnit.unit = ofOverMap (identityCoverHom T) ≫ u :=
  rfl

/-- Compatibility of a covering member of a refinement with the structure maps to `S`. -/
theorem coverMap_w {S : Scheme.{u}} {T : Over S} {ι ι' : Type u}
    {family : ι → Over T.left} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j : ι') :
    (φ j).left ≫ (coverOver family (α j)).hom = (coverOver family' j).hom :=
  sorry

/-- The morphism `T'_j ⟶ T_{α(j)}` of a refinement, as a map of schemes over `S`. -/
def coverMap {S : Scheme.{u}} {T : Over S} {ι ι' : Type u}
    {family : ι → Over T.left} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j : ι') :
    coverOver family' j ⟶ coverOver family (α j) :=
  Over.homMk (φ j).left (coverMap_w α φ j)

/-- A refinement map commutes with the structure morphisms to `T`. -/
theorem coverMap_coverHom {S : Scheme.{u}} {T : Over S} {ι ι' : Type u}
    {family : ι → Over T.left} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j : ι') :
    coverMap α φ j ≫ coverHom family (α j) = coverHom family' j :=
  sorry

/-- Underlying scheme map of a pairwise refinement. -/
def pairMapScheme {S : Scheme.{u}} {T : Over S} {ι ι' : Type u}
    {family : ι → Over T.left} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j j' : ι') :
    (pairOver family' j j').left ⟶ (pairOver family (α j) (α j')).left :=
  pullback.map (family' j).hom (family' j').hom (family (α j)).hom (family (α j')).hom
    (φ j).left (φ j').left (𝟙 T.left)
    ((Category.comp_id (family' j).hom).trans (Over.w (φ j)).symm)
    ((Category.comp_id (family' j').hom).trans (Over.w (φ j')).symm)

/-- `pairMapScheme` lies over `S`. -/
theorem pairMap_w {S : Scheme.{u}} {T : Over S} {ι ι' : Type u}
    {family : ι → Over T.left} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j j' : ι') :
    pairMapScheme α φ j j' ≫ (pairOver family (α j) (α j')).hom =
      (pairOver family' j j').hom :=
  sorry

/-- The morphism `T'_j ×_T T'_{j'} ⟶ T_{α(j)} ×_T T_{α(j')}` of a refinement. -/
def pairMap {S : Scheme.{u}} {T : Over S} {ι ι' : Type u}
    {family : ι → Over T.left} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j j' : ι') :
    pairOver family' j j' ⟶ pairOver family (α j) (α j') :=
  Over.homMk (pairMapScheme α φ j j') (pairMap_w α φ j j')

/-- The prescribed component maps satisfy the endpoint and cocycle equations. -/
private theorem pullback_laws {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left} (D : DescentDatum G family)
    {ι' : Type u} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) :
    let u : ∀ i, ofOver (coverOver family' i) ⟶ G.U.left := fun j ↦ ofOverMap (coverMap α φ j) ≫ D.u (α j)
    let r : ∀ i j, ofOver (pairOver family' i j) ⟶ G.R.left := fun j j' ↦ ofOverMap (pairMap α φ j j') ≫ D.r (α j) (α j')
    (∀ i j, r i j ≫ G.s.left = ofOverMap (pr0 family' i j) ≫ u i) ∧
      (∀ i j, r i j ≫ G.t.left = ofOverMap (pr1 family' i j) ≫ u j) ∧
        ∀ i j k
          (h :
            (ofOverMap (pr12 family' i j k) ≫ r j k) ≫ G.s.left =
              (ofOverMap (pr01 family' i j k) ≫ r i j) ≫ G.t.left),
          G.compArrows (ofOverMap (pr12 family' i j k) ≫ r j k)
              (ofOverMap (pr01 family' i j k) ≫ r i j) h =
            ofOverMap (pr02 family' i j k) ≫ r i k := sorry

/-- Pullback of a descent datum along a refinement `α, φ` of indexed families over `T`. -/
def pullback {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left} (D : DescentDatum G family)
    {ι' : Type u} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) :
    DescentDatum G family' where
  u := fun j ↦ ofOverMap (coverMap α φ j) ≫ D.u (α j)
  r := fun j j' ↦ ofOverMap (pairMap α φ j j') ≫ D.r (α j) (α j')
  source := (pullback_laws D α φ).1
  target := (pullback_laws D α φ).2.1
  cocycle := (pullback_laws D α φ).2.2

/-- Object maps of a pulled-back descent datum are `u_{α(j)} ∘ φ_j`. -/
theorem pullback_u {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left} (D : DescentDatum G family)
    {ι' : Type u} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j : ι') :
    (D.pullback α φ).u j = ofOverMap (coverMap α φ j) ≫ D.u (α j) :=
  rfl

/-- Arrow maps of a pulled-back descent datum are `r_{α(j)α(j')} ∘ (φ_j × φ_{j'})`. -/
theorem pullback_r {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left} (D : DescentDatum G family)
    {ι' : Type u} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j j' : ι') :
    (D.pullback α φ).r j j' = ofOverMap (pairMap α φ j j') ≫ D.r (α j) (α j') :=
  rfl

/-- A morphism of `[U/R]`-descent data over a fixed indexed family. -/
structure Hom {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    (D D' : DescentDatum G family) where
  /-- The component arrows `r_i : T_i ⟶ R`. -/
  r : ∀ i, ofOver (coverOver family i) ⟶ G.R.left
  /-- Source law `(α)`: `u_i = s ∘ r_i`. -/
  source : ∀ i, D.u i = r i ≫ G.s.left
  /-- Target law `(α)`: `u'_i = t ∘ r_i`. -/
  target : ∀ i, D'.u i = r i ≫ G.t.left
  /-- Compatibility `(β)`: `c ∘ (r'_ij, r_i ∘ pr₀) = c ∘ (r_j ∘ pr₁, r_ij)`. -/
  compat :
    ∀ i j
      (h₁ :
        D'.r i j ≫ G.s.left =
          (ofOverMap (pr0 family i j) ≫ r i) ≫ G.t.left)
      (h₂ :
        (ofOverMap (pr1 family i j) ≫ r j) ≫ G.s.left =
          D.r i j ≫ G.t.left),
      G.compArrows (D'.r i j) (ofOverMap (pr0 family i j) ≫ r i) h₁ =
        G.compArrows (ofOverMap (pr1 family i j) ≫ r j) (D.r i j) h₂

namespace Hom

/-- Source and compatibility laws of a morphism of descent data. -/
theorem spec {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' : DescentDatum G family} (ψ : Hom D D') :
    (∀ i, D.u i = ψ.r i ≫ G.s.left ∧ D'.u i = ψ.r i ≫ G.t.left) ∧
      ∀ i j
        (h₁ :
          D'.r i j ≫ G.s.left =
            (ofOverMap (pr0 family i j) ≫ ψ.r i) ≫ G.t.left)
        (h₂ :
          (ofOverMap (pr1 family i j) ≫ ψ.r j) ≫ G.s.left =
            D.r i j ≫ G.t.left),
        G.compArrows (D'.r i j) (ofOverMap (pr0 family i j) ≫ ψ.r i) h₁ =
          G.compArrows (ofOverMap (pr1 family i j) ≫ ψ.r j) (D.r i j) h₂ :=
  ⟨fun i ↦ ⟨ψ.source i, ψ.target i⟩, ψ.compat⟩

/-- The prescribed component maps satisfy the endpoint and compatibility equations. -/
private theorem id_laws {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left} (D : DescentDatum G family) :
    let r : ∀ i, ofOver (coverOver family i) ⟶ G.R.left := fun i ↦ D.u i ≫ G.e.left
    (∀ i, D.u i = r i ≫ G.s.left ∧ D.u i = r i ≫ G.t.left) ∧
      ∀ i j
        (h₁ :
          D.r i j ≫ G.s.left =
            (ofOverMap (pr0 family i j) ≫ r i) ≫ G.t.left)
        (h₂ :
          (ofOverMap (pr1 family i j) ≫ r j) ≫ G.s.left =
            D.r i j ≫ G.t.left),
        G.compArrows (D.r i j) (ofOverMap (pr0 family i j) ≫ r i) h₁ =
          G.compArrows (ofOverMap (pr1 family i j) ≫ r j) (D.r i j) h₂ := sorry

/-- Identity morphism of a descent datum, with components `e ∘ u_i`. -/
def id {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left} (D : DescentDatum G family) :
    Hom D D where
  r := fun i ↦ D.u i ≫ G.e.left
  source := fun i ↦ ((id_laws D).1 i).1
  target := fun i ↦ ((id_laws D).1 i).2
  compat := (id_laws D).2

/-- Components of the identity morphism are `e ∘ u_i`. -/
theorem id_r {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left} (D : DescentDatum G family) (i : ι) :
    (Hom.id D).r i = D.u i ≫ G.e.left :=
  rfl

/-- Composability of component arrows of two morphisms of descent data. -/
theorem comp_composable {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' D'' : DescentDatum G family} (ψ : Hom D D') (ψ' : Hom D' D'') (i : ι) :
    ψ'.r i ≫ G.s.left = ψ.r i ≫ G.t.left :=
  sorry

/-- The prescribed component maps satisfy the endpoint and compatibility equations. -/
private theorem comp_laws {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' D'' : DescentDatum G family} (ψ : Hom D D') (ψ' : Hom D' D'') :
    let r : ∀ i, ofOver (coverOver family i) ⟶ G.R.left := fun i ↦ G.compArrows (ψ'.r i) (ψ.r i) (comp_composable ψ ψ' i)
    (∀ i, D.u i = r i ≫ G.s.left ∧ D''.u i = r i ≫ G.t.left) ∧
      ∀ i j
        (h₁ :
          D''.r i j ≫ G.s.left =
            (ofOverMap (pr0 family i j) ≫ r i) ≫ G.t.left)
        (h₂ :
          (ofOverMap (pr1 family i j) ≫ r j) ≫ G.s.left =
            D.r i j ≫ G.t.left),
        G.compArrows (D''.r i j) (ofOverMap (pr0 family i j) ≫ r i) h₁ =
          G.compArrows (ofOverMap (pr1 family i j) ≫ r j) (D.r i j) h₂ := sorry

/-- Composition of morphisms of descent data, with components `c ∘ (r'_i, r_i)`. -/
def comp {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' D'' : DescentDatum G family} (ψ : Hom D D') (ψ' : Hom D' D'') :
    Hom D D'' where
  r := fun i ↦ G.compArrows (ψ'.r i) (ψ.r i) (comp_composable ψ ψ' i)
  source := fun i ↦ ((comp_laws ψ ψ').1 i).1
  target := fun i ↦ ((comp_laws ψ ψ').1 i).2
  compat := (comp_laws ψ ψ').2

/-- The prescribed component maps satisfy the endpoint and compatibility equations. -/
private theorem inv_laws {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' : DescentDatum G family} (ψ : Hom D D') :
    let r : ∀ i, ofOver (coverOver family i) ⟶ G.R.left := fun i ↦ ψ.r i ≫ G.i.left
    (∀ i, D'.u i = r i ≫ G.s.left ∧ D.u i = r i ≫ G.t.left) ∧
      ∀ i j
        (h₁ :
          D.r i j ≫ G.s.left =
            (ofOverMap (pr0 family i j) ≫ r i) ≫ G.t.left)
        (h₂ :
          (ofOverMap (pr1 family i j) ≫ r j) ≫ G.s.left =
            D'.r i j ≫ G.t.left),
        G.compArrows (D.r i j) (ofOverMap (pr0 family i j) ≫ r i) h₁ =
          G.compArrows (ofOverMap (pr1 family i j) ≫ r j) (D'.r i j) h₂ := sorry

/-- Inverse of a morphism of descent data, with components `i ∘ r_i`. -/
def inv {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' : DescentDatum G family} (ψ : Hom D D') :
    Hom D' D where
  r := fun i ↦ ψ.r i ≫ G.i.left
  source := fun i ↦ ((inv_laws ψ).1 i).1
  target := fun i ↦ ((inv_laws ψ).1 i).2
  compat := (inv_laws ψ).2

/-- Components of the inverse morphism are `i ∘ r_i`. -/
theorem inv_r {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' : DescentDatum G family} (ψ : Hom D D') (i : ι) :
    (ψ.inv).r i = ψ.r i ≫ G.i.left :=
  rfl

/-- The prescribed component maps satisfy the endpoint and compatibility equations. -/
private theorem pullback_laws {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' : DescentDatum G family} (ψ : Hom D D')
    {ι' : Type u} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) :
    let r : ∀ i, ofOver (coverOver family' i) ⟶ G.R.left := fun j ↦ ofOverMap (coverMap α φ j) ≫ ψ.r (α j)
    (∀ i, (D.pullback α φ).u i = r i ≫ G.s.left ∧ (D'.pullback α φ).u i = r i ≫ G.t.left) ∧
      ∀ i j
        (h₁ :
          (D'.pullback α φ).r i j ≫ G.s.left =
            (ofOverMap (pr0 family' i j) ≫ r i) ≫ G.t.left)
        (h₂ :
          (ofOverMap (pr1 family' i j) ≫ r j) ≫ G.s.left =
            (D.pullback α φ).r i j ≫ G.t.left),
        G.compArrows ((D'.pullback α φ).r i j) (ofOverMap (pr0 family' i j) ≫ r i) h₁ =
          G.compArrows (ofOverMap (pr1 family' i j) ≫ r j) ((D.pullback α φ).r i j) h₂ := sorry

/-- Pullback of a morphism of descent data along a refinement of indexed families. -/
def pullback {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' : DescentDatum G family} (ψ : Hom D D')
    {ι' : Type u} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) :
    Hom (D.pullback α φ) (D'.pullback α φ) where
  r := fun j ↦ ofOverMap (coverMap α φ j) ≫ ψ.r (α j)
  source := fun i ↦ ((pullback_laws ψ α φ).1 i).1
  target := fun i ↦ ((pullback_laws ψ α φ).1 i).2
  compat := (pullback_laws ψ α φ).2

end Hom

end DescentDatum

/-- The overlap arrow `r` realises the canonical composite of the given fibre isomorphisms as
`π(r)`, after the source and target laws. -/
def IsPiArrow {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (x : (fppfQuotientStack G).p.Fiber T)
    (u : ∀ i, ofOver (coverOver family i) ⟶ G.U.left)
    (e : ∀ i, atlasObj G (u i) ≅ Chosen.reindexObj (fppfQuotientStack G).p (coverHom family i) x)
    {i j : ι} (r : ofOver (pairOver family i j) ⟶ G.R.left) : Prop :=
  ∃ (hs : r ≫ G.s.left = ofOverMap (pr0 family i j) ≫ u i)
    (ht : r ≫ G.t.left = ofOverMap (pr1 family i j) ≫ u j),
    (sourceComparison G family (u i) hs).hom ≫
        Chosen.reindexMap (fppfQuotientStack G).p (pr0 family i j) (e i).hom ≫
        (overlapAssociator G family x i j).hom ≫
        Chosen.reindexMap (fppfQuotientStack G).p (pr1 family i j) (e j).inv ≫
        (targetComparison G family (u j) ht).inv =
      atlasArrow G r

/-- `IsPiArrow` records the source and target laws together with equality of `atlasArrow r`
against the named canonical composite. -/
theorem isPiArrow_spec {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (x : (fppfQuotientStack G).p.Fiber T)
    (u : ∀ i, ofOver (coverOver family i) ⟶ G.U.left)
    (e : ∀ i, atlasObj G (u i) ≅ Chosen.reindexObj (fppfQuotientStack G).p (coverHom family i) x)
    {i j : ι} (r : ofOver (pairOver family i j) ⟶ G.R.left) :
    IsPiArrow G family x u e (i := i) (j := j) r ↔
      ∃ (hs : r ≫ G.s.left = ofOverMap (pr0 family i j) ≫ u i)
        (ht : r ≫ G.t.left = ofOverMap (pr1 family i j) ≫ u j),
        (sourceComparison G family (u i) hs).hom ≫
            Chosen.reindexMap (fppfQuotientStack G).p (pr0 family i j) (e i).hom ≫
            (overlapAssociator G family x i j).hom ≫
            Chosen.reindexMap (fppfQuotientStack G).p (pr1 family i j) (e j).inv ≫
            (targetComparison G family (u j) ht).inv =
          atlasArrow G r := by
  unfold IsPiArrow
  with_reducible exact Iff.rfl

/-- An object of `[U/R]_T` corresponds to a `[U/R]`-descent datum when each restriction is
`π(u_i)` via chosen fibre isomorphisms and each overlap isomorphism is `π(r_ij)`. -/
structure Corresponds {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (x : (fppfQuotientStack G).p.Fiber T) (D : DescentDatum G family) where
  /-- The fibre isomorphisms `π(u_i) ≅ f_i^* x`. -/
  e : ∀ i, atlasObj G (D.u i) ≅ Chosen.reindexObj (fppfQuotientStack G).p (coverHom family i) x
  /-- Each overlap arrow realises the named canonical composite as `π(r_ij)`. -/
  overlap : ∀ i j, IsPiArrow G family x D.u e (D.r i j)

namespace Corresponds

/-- A correspondence supplies fibre isomorphisms realising each overlap arrow as `π(r_ij)`. -/
theorem spec {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {x : (fppfQuotientStack G).p.Fiber T} {D : DescentDatum G family}
    (h : Corresponds G family x D) :
    ∀ i j, IsPiArrow G family x D.u h.e (D.r i j) :=
  h.overlap

/-- Reindexing the local presentation isomorphisms preserves the specified overlap arrows. -/
private theorem pullback_overlap {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {x : (fppfQuotientStack G).p.Fiber T} {D : DescentDatum G family}
    (h : Corresponds G family x D) {ι' : Type u} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) :
    let e : ∀ j, atlasObj G ((D.pullback α φ).u j) ≅
        Chosen.reindexObj (fppfQuotientStack G).p (coverHom family' j) x :=
      fun j ↦
        atlasObjReindexIso G (DescentDatum.coverMap α φ j) (D.u (α j)) ≪≫
          (Chosen.reindex (fppfQuotientStack G).p (DescentDatum.coverMap α φ j)).mapIso (h.e (α j)) ≪≫
          (Chosen.Reindex.specifiedCompIsoApp (fppfQuotientStack G).p
              (coverHom family (α j)) (DescentDatum.coverMap α φ j)
              (DescentDatum.coverMap α φ j ≫ coverHom family (α j)) rfl x).symm ≪≫
          Chosen.Reindex.congrIsoApp (fppfQuotientStack G).p
            (DescentDatum.coverMap_coverHom α φ j) x
    ∀ i j, IsPiArrow G family' x (D.pullback α φ).u e ((D.pullback α φ).r i j) := sorry

/-- Pull a correspondence back along a refinement of indexed families. -/
def pullback {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {x : (fppfQuotientStack G).p.Fiber T} {D : DescentDatum G family}
    (h : Corresponds G family x D) {ι' : Type u} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) :
    Corresponds G family' x (D.pullback α φ) where
  e := fun j ↦
    atlasObjReindexIso G (DescentDatum.coverMap α φ j) (D.u (α j)) ≪≫
      (Chosen.reindex (fppfQuotientStack G).p (DescentDatum.coverMap α φ j)).mapIso (h.e (α j)) ≪≫
      (Chosen.Reindex.specifiedCompIsoApp (fppfQuotientStack G).p
          (coverHom family (α j)) (DescentDatum.coverMap α φ j)
          (DescentDatum.coverMap α φ j ≫ coverHom family (α j)) rfl x).symm ≪≫
      Chosen.Reindex.congrIsoApp (fppfQuotientStack G).p
        (DescentDatum.coverMap_coverHom α φ j) x
  overlap := pullback_overlap h α φ

set_option maxHeartbeats 800000 in
/-- The pulled-back fibre isomorphism at `j` is the reindexing of `h.e (α j)` along `φ_j`. -/
theorem pullback_e {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {x : (fppfQuotientStack G).p.Fiber T} {D : DescentDatum G family}
    (h : Corresponds G family x D) {ι' : Type u} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j : ι') :
    (h.pullback α φ).e j =
      atlasObjReindexIso G (DescentDatum.coverMap α φ j) (D.u (α j)) ≪≫
        (Chosen.reindex (fppfQuotientStack G).p (DescentDatum.coverMap α φ j)).mapIso (h.e (α j)) ≪≫
        (Chosen.Reindex.specifiedCompIsoApp (fppfQuotientStack G).p
            (coverHom family (α j)) (DescentDatum.coverMap α φ j)
            (DescentDatum.coverMap α φ j ≫ coverHom family (α j)) rfl x).symm ≪≫
        Chosen.Reindex.congrIsoApp (fppfQuotientStack G).p
          (DescentDatum.coverMap_coverHom α φ j) x := by
  dsimp only [pullback]
  rfl

end Corresponds

/-- Unfolding of `Corresponds` as chosen fibre isomorphisms realising the overlap arrows as
`π(r_ij)`. -/
theorem corresponds_iff {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (x : (fppfQuotientStack G).p.Fiber T) (D : DescentDatum G family) :
    Nonempty (Corresponds G family x D) ↔
      ∃ e : ∀ i, atlasObj G (D.u i) ≅ Chosen.reindexObj (fppfQuotientStack G).p (coverHom family i) x,
        ∀ i j, IsPiArrow G family x D.u e (D.r i j) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.e, h.overlap⟩
  · rintro ⟨e, h⟩
    exact ⟨⟨e, h⟩⟩

/-- A morphism of descent data agrees with a fibre morphism when each component is `π(r_i)`
after conjugating by the chosen correspondence isomorphisms. -/
def DescentDatum.Hom.agreesWith {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' : DescentDatum G family} (ψ : DescentDatum.Hom D D')
    {x y : (fppfQuotientStack G).p.Fiber T}
    (hx : Corresponds G family x D) (hy : Corresponds G family y D') (φ : x ⟶ y) : Prop :=
  ∀ i,
    (sourceHomComparison G (D.u i) (ψ.r i) (ψ.source i)).hom ≫
        (hx.e i).hom ≫ Chosen.reindexMap (fppfQuotientStack G).p (coverHom family i) φ ≫ (hy.e i).inv ≫
        (targetHomComparison G (D'.u i) (ψ.r i) (ψ.target i)).inv =
      atlasArrow G (ψ.r i)

/-- `agreesWith` is conjugation of the restricted fibre morphism by the chosen correspondence
isomorphisms. -/
theorem DescentDatum.Hom.agreesWith_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' : DescentDatum G family} (ψ : DescentDatum.Hom D D')
    {x y : (fppfQuotientStack G).p.Fiber T}
    (hx : Corresponds G family x D) (hy : Corresponds G family y D') (φ : x ⟶ y) :
    ψ.agreesWith hx hy φ ↔
      ∀ i,
        (sourceHomComparison G (D.u i) (ψ.r i) (ψ.source i)).hom ≫
            (hx.e i).hom ≫ Chosen.reindexMap (fppfQuotientStack G).p (coverHom family i) φ ≫ (hy.e i).inv ≫
            (targetHomComparison G (D'.u i) (ψ.r i) (ψ.target i)).inv =
          atlasArrow G (ψ.r i) := by
  unfold DescentDatum.Hom.agreesWith
  with_reducible exact Iff.rfl

/-- Every fibre object of the fppf quotient stack is fppf-locally isomorphic to an atlas point. -/
theorem exists_fppfCovering_atlasIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} (x : (fppfQuotientStack G).p.Fiber T) :
    ∃ (ι : Type u) (family : ι → Over T.left)
      (u : ∀ i, ofOver (coverOver family i) ⟶ G.U.left),
      Scheme.FppfCovering family ∧
        ∀ i, Nonempty (atlasObj G (u i) ≅ Chosen.reindexObj (fppfQuotientStack G).p (coverHom family i) x) :=
  sorry

/-- The canonical overlap composites of local atlas presentations are induced by arrow-space points. -/
theorem exists_arrow_of_composedIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (x : (fppfQuotientStack G).p.Fiber T)
    (u : ∀ i, ofOver (coverOver family i) ⟶ G.U.left)
    (e : ∀ i, atlasObj G (u i) ≅ Chosen.reindexObj (fppfQuotientStack G).p (coverHom family i) x) :
    ∃ r : ∀ i j, ofOver (pairOver family i j) ⟶ G.R.left,
      ∀ i j, IsPiArrow G family x u e (r i j) :=
  sorry

/-- Arrow-space points inducing the canonical overlap composites satisfy the descent equations. -/
theorem isDescentDatum_of_atlasIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (x : (fppfQuotientStack G).p.Fiber T)
    (u : ∀ i, ofOver (coverOver family i) ⟶ G.U.left)
    (e : ∀ i, atlasObj G (u i) ≅ Chosen.reindexObj (fppfQuotientStack G).p (coverHom family i) x)
    (r : ∀ i j, ofOver (pairOver family i j) ⟶ G.R.left)
    (hπ : ∀ i j, IsPiArrow G family x u e (r i j)) :
    ∃ D : DescentDatum G family, D.u = u ∧ D.r = r :=
  sorry

/-- Every explicit descent datum on an fppf covering comes from a fibre object of the quotient stack. -/
theorem exists_fiberObj_of_descentDatum {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (h_covering : Scheme.FppfCovering family) (D : DescentDatum G family) :
    ∃ x : (fppfQuotientStack G).p.Fiber T, Nonempty (Corresponds G family x D) :=
  sorry

/-- Fibre morphisms correspond uniquely in both directions to morphisms of their explicit descent data. -/
theorem fiberHom_existsUnique {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (h_covering : Scheme.FppfCovering family)
    {x y : (fppfQuotientStack G).p.Fiber T} {D D' : DescentDatum G family}
    (hx : Corresponds G family x D) (hy : Corresponds G family y D') :
    (∀ φ : x ⟶ y, ∃! ψ : DescentDatum.Hom D D', ψ.agreesWith hx hy φ) ∧
      ∀ ψ : DescentDatum.Hom D D', ∃! φ : x ⟶ y, ψ.agreesWith hx hy φ :=
  sorry

/-- Agreement between fibre morphisms and descent morphisms is preserved and reflected by fppf refinement. -/
theorem corresponds_pullback {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (h_covering : Scheme.FppfCovering family)
    {x : (fppfQuotientStack G).p.Fiber T} {D : DescentDatum G family}
    (hx : Corresponds G family x D) {ι' : Type u} (family' : ι' → Over T.left)
    (h_covering' : Scheme.FppfCovering family')
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) :
    (∀ {y : (fppfQuotientStack G).p.Fiber T} {D' : DescentDatum G family}
        (hy : Corresponds G family y D') (φhom : x ⟶ y) (ψ : DescentDatum.Hom D D'),
        ψ.agreesWith hx hy φhom →
          (ψ.pullback α φ).agreesWith (hx.pullback α φ) (hy.pullback α φ) φhom) ∧
      ∀ {y : (fppfQuotientStack G).p.Fiber T} {D' : DescentDatum G family}
        (hy : Corresponds G family y D') (φhom : x ⟶ y) (ψ : DescentDatum.Hom D D'),
        (ψ.pullback α φ).agreesWith (hx.pullback α φ) (hy.pullback α φ) φhom →
          ψ.agreesWith hx hy φhom :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
