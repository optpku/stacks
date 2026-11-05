/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.IndexedCover
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
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
# Atlas and overlap comparisons for quotient stacks

Explicit fibre objects and arrows of the quotient atlas and their canonical
comparisons with reindexing along an indexed cover.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits Opposite
open Functor
open CategoryTheory.CategoryOfElements

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

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
theorem atlasSourceFiberIso_over {S : Scheme.{u}} {B : AlgebraicSpace S}
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
theorem atlasTargetFiberIso_over {S : Scheme.{u}} {B : AlgebraicSpace S}
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
def overlapTargetComparison {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
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

/-- `overlapTargetComparison` is the composite of `atlasTargetFiberIso`, `objOfHomMapIso`, and
`atlasObjReindexIso`. -/
theorem overlapTargetComparison_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} {ι : Type u}
    (family : ι → Over T.left) {i j : ι}
    (u : ofOver (coverOver family j) ⟶ G.U.left)
    {r : ofOver (pairOver family i j) ⟶ G.R.left}
    (ht : r ≫ G.t.left = ofOverMap (pr1 family i j) ≫ u) :
    overlapTargetComparison G family u ht =
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

end AlgebraicGeometry.GroupoidAlgebraicSpace
