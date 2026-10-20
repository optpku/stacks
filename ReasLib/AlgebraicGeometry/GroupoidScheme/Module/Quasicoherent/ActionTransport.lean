/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent

/-!
# Transporting actions on equivariant quasi-coherent modules

This module transports equivariance data across an isomorphism of the underlying
quasi-coherent modules and constructs the resulting isomorphism of equivariant objects.
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace AlgebraicGeometry.GroupoidScheme.QCoh

/-- Conjugate the action of an equivariant quasi-coherent module along an isomorphism of
underlying quasi-coherent modules. -/
abbrev transportedAction {S : Scheme.{u}} {G : GroupoidScheme S}
    (E : G.QCoh) {Y : Scheme.QCoh G.U.left} (e : Y ≅ E.obj) :
    (Scheme.QCoh.pullback G.t.left).obj Y ⟶
      (Scheme.QCoh.pullback G.s.left).obj Y :=
  (Scheme.QCoh.pullback G.t.left).map e.hom ≫
    E.action ≫
      (Scheme.QCoh.pullback G.s.left).map e.inv

/-- Reindexing a transported action conjugates the reindexed original action. -/
theorem reindexAction_transportedAction {S : Scheme.{u}} {G : GroupoidScheme S}
    (E : G.QCoh) {Y : Scheme.QCoh G.U.left} (e : Y ≅ E.obj)
    {Z : Scheme.{u}} (h : Z ⟶ G.R.left) :
    GroupoidScheme.reindexAction G.t.left G.s.left h Y (transportedAction E e) =
      (Scheme.QCoh.pullback (h ≫ G.t.left)).map e.hom ≫
        GroupoidScheme.reindexAction G.t.left G.s.left h E.obj E.action ≫
          (Scheme.QCoh.pullback (h ≫ G.s.left)).map e.inv := sorry

/-- The transported action satisfies the cocycle and unit conditions. -/
theorem transportedAction_spec {S : Scheme.{u}} {G : GroupoidScheme S}
    (E : G.QCoh) {Y : Scheme.QCoh G.U.left} (e : Y ≅ E.obj) :
    Cocycle G Y (transportedAction E e) ∧ Unit G Y (transportedAction E e) := sorry

/-- Replace the underlying quasi-coherent module of an equivariant object by an isomorphic
one, transporting its action along the given isomorphism. -/
def rebaseAlongIso {S : Scheme.{u}} {G : GroupoidScheme S}
    (E : G.QCoh) {Y : Scheme.QCoh G.U.left} (e : Y ≅ E.obj) : G.QCoh :=
  of Y (transportedAction E e)
    (transportedAction_spec E e).1 (transportedAction_spec E e).2

/-- The forward map from a rebased equivariant object to the original object is compatible
with their actions. -/
theorem rebaseAlongIso_hom_compatibility {S : Scheme.{u}} {G : GroupoidScheme S}
    (E : G.QCoh) {Y : Scheme.QCoh G.U.left} (e : Y ≅ E.obj) :
    (Scheme.QCoh.pullback G.t.left).map e.hom ≫ E.action =
      (rebaseAlongIso E e).action ≫ (Scheme.QCoh.pullback G.s.left).map e.hom := by
  change (Scheme.QCoh.pullback G.t.left).map e.hom ≫ E.action =
    ((Scheme.QCoh.pullback G.t.left).map e.hom ≫
      E.action ≫ (Scheme.QCoh.pullback G.s.left).map e.inv) ≫
        (Scheme.QCoh.pullback G.s.left).map e.hom
  simp

/-- The inverse map from the original equivariant object to its rebasing is compatible with
their actions. -/
theorem rebaseAlongIso_inv_compatibility {S : Scheme.{u}} {G : GroupoidScheme S}
    (E : G.QCoh) {Y : Scheme.QCoh G.U.left} (e : Y ≅ E.obj) :
    (Scheme.QCoh.pullback G.t.left).map e.inv ≫ (rebaseAlongIso E e).action =
      E.action ≫ (Scheme.QCoh.pullback G.s.left).map e.inv := by
  change (Scheme.QCoh.pullback G.t.left).map e.inv ≫
      ((Scheme.QCoh.pullback G.t.left).map e.hom ≫
        E.action ≫ (Scheme.QCoh.pullback G.s.left).map e.inv) =
    E.action ≫ (Scheme.QCoh.pullback G.s.left).map e.inv
  simp

/-- Rebasing an equivariant quasi-coherent module along an isomorphism of its underlying
quasi-coherent module produces an isomorphic equivariant object. -/
def rebaseAlongIsoIso {S : Scheme.{u}} {G : GroupoidScheme S}
    (E : G.QCoh) {Y : Scheme.QCoh G.U.left} (e : Y ≅ E.obj) :
    rebaseAlongIso E e ≅ E :=
  { hom := GroupoidScheme.System.Hom.of e.hom (rebaseAlongIso_hom_compatibility E e)
    inv := GroupoidScheme.System.Hom.of e.inv (rebaseAlongIso_inv_compatibility E e)
    hom_inv_id := GroupoidScheme.System.Hom.ext e.hom_inv_id
    inv_hom_id := GroupoidScheme.System.Hom.ext e.inv_hom_id }

end AlgebraicGeometry.GroupoidScheme.QCoh
