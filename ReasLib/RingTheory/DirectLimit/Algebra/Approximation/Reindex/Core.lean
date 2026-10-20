/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation
public import ReasLib.RingTheory.DirectLimit.Reindex.Core
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Core data for reindexed algebra approximations

This leaf owns pulling a directed approximation and its finite-type data back
along an explicit order isomorphism.  Colimit, base-change, and optional
property transport are independent companion layers.
-/

@[expose] public section

universe u v x

noncomputable section

namespace Ring.DirectLimit.Algebra.Approximation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace Hom

variable {f : R →+* S}

/-- Reindex a directed ring-hom approximation along an order isomorphism. -/
@[stacks 00R1 "reindexed directed approximation"]
noncomputable def reindex (A : Hom f) {J : Type x} [Preorder J]
    (e : J ≃o A.index) : Hom f where
  index := J
  preorder := inferInstance
  indexNonempty := Nonempty.map e.symm A.indexNonempty
  directedOrder := OrderIso.isDirectedOrder e
  source := fun j ↦ A.source (e j)
  target := fun j ↦ A.target (e j)
  sourceCommRing := fun _ ↦ inferInstance
  targetCommRing := fun _ ↦ inferInstance
  sourceMap := fun j k h ↦ A.sourceMap (e j) (e k) (e.monotone h)
  targetMap := fun j k h ↦ A.targetMap (e j) (e k) (e.monotone h)
  sourceDirectedSystem :=
    DirectedSystem.reindex e (fun i j h ↦ A.sourceMap i j h)
  targetDirectedSystem :=
    DirectedSystem.reindex e (fun i j h ↦ A.targetMap i j h)
  map := fun j ↦ A.map (e j)
  map_comm := fun h ↦ A.map_comm (e.monotone h)
  sourceColimit :=
    (Ring.DirectLimit.Reindex.equiv e
      (fun i j h ↦ A.sourceMap i j h)).trans A.sourceColimit
  targetColimit :=
    (Ring.DirectLimit.Reindex.equiv e
      (fun i j h ↦ A.targetMap i j h)).trans A.targetColimit
  colimit_comm := sorry

/-- Reindexing pulls the source family back along the order isomorphism. -/
@[simp, stacks 00R1 "reindexed directed approximation"]
theorem reindex_source (A : Hom f) {J : Type x} [Preorder J]
    (e : J ≃o A.index) :
    (A.reindex e).source = fun j ↦ A.source (e j) := sorry

/-- Reindexing pulls the target family back along the order isomorphism. -/
@[simp, stacks 00R1 "reindexed directed approximation"]
theorem reindex_target (A : Hom f) {J : Type x} [Preorder J]
    (e : J ≃o A.index) :
    (A.reindex e).target = fun j ↦ A.target (e j) := sorry

/-- The stage map in a reindexed approximation is the original map at the
corresponding stage. -/
@[simp, stacks 00R1 "reindexed directed approximation"]
theorem reindex_map (A : Hom f) {J : Type x} [Preorder J]
    (e : J ≃o A.index) (j : J) :
    (A.reindex e).map j = A.map (e j) := sorry

/-- Reindexed stage maps evaluate as the corresponding original stage maps. -/
@[simp, stacks 00R1 "reindexed directed approximation"]
theorem reindex_map_apply (A : Hom f) {J : Type x} [Preorder J]
    (e : J ≃o A.index) (j : J) (a : A.source (e j)) :
    (A.reindex e).map j a = A.map (e j) a := sorry

/-- A reindexed source transition is the corresponding original source
transition. -/
@[simp, stacks 00R1 "reindexed directed approximation"]
theorem reindex_sourceMap (A : Hom f) {J : Type x} [Preorder J]
    (e : J ≃o A.index) {j k : J} (h : j ≤ k) :
    (A.reindex e).sourceMap j k h =
      A.sourceMap (e j) (e k) (e.monotone h) := sorry

/-- A reindexed target transition is the corresponding original target
transition. -/
@[simp, stacks 00R1 "reindexed directed approximation"]
theorem reindex_targetMap (A : Hom f) {J : Type x} [Preorder J]
    (e : J ≃o A.index) {j k : J} (h : j ≤ k) :
    (A.reindex e).targetMap j k h =
      A.targetMap (e j) (e k) (e.monotone h) := sorry

/-- Reindexed source transitions evaluate as the corresponding original
transitions. -/
@[simp, stacks 00R1 "reindexed directed approximation"]
theorem reindex_sourceMap_apply (A : Hom f) {J : Type x}
    [Preorder J] (e : J ≃o A.index) {j k : J} (h : j ≤ k)
    (a : A.source (e j)) :
    (A.reindex e).sourceMap j k h a =
      A.sourceMap (e j) (e k) (e.monotone h) a := sorry

/-- Reindexed target transitions evaluate as the corresponding original
transitions. -/
@[simp, stacks 00R1 "reindexed directed approximation"]
theorem reindex_targetMap_apply (A : Hom f) {J : Type x}
    [Preorder J] (e : J ≃o A.index) {j k : J} (h : j ≤ k)
    (b : A.target (e j)) :
    (A.reindex e).targetMap j k h b =
      A.targetMap (e j) (e k) (e.monotone h) b := sorry

end Hom

namespace FiniteType

variable {f : R →+* S}

/-- Reindex a finite-type directed approximation along an order isomorphism. -/
@[stacks 00R1 "reindexed finite-type approximation"]
noncomputable def reindex (A : FiniteType f) {J : Type x}
    [Preorder J] (e : J ≃o A.index) : FiniteType f where
  toHom := A.toHom.reindex e
  sourceFiniteType := fun j ↦ A.sourceFiniteType (e j)
  mapFiniteType := fun j ↦ A.mapFiniteType (e j)

/-- Forgetting finite-type data commutes with reindexing. -/
@[simp, stacks 00R1 "reindexed finite-type approximation"]
theorem reindex_toHom (A : FiniteType f) {J : Type x}
    [Preorder J] (e : J ≃o A.index) :
    (A.reindex e).toHom = A.toHom.reindex e := sorry

/-- The stage map of a reindexed finite-type approximation is the original
stage map at the corresponding index. -/
@[simp, stacks 00R1 "reindexed finite-type approximation"]
theorem reindex_map (A : FiniteType f) {J : Type x}
    [Preorder J] (e : J ≃o A.index) (j : J) :
    (A.reindex e).map j = A.map (e j) := sorry

/-- Reindexed finite-type stage maps agree pointwise with the original maps. -/
@[simp, stacks 00R1 "reindexed finite-type approximation"]
theorem reindex_map_apply (A : FiniteType f) {J : Type x}
    [Preorder J] (e : J ≃o A.index) (j : J) (a : A.source (e j)) :
    (A.reindex e).map j a = A.map (e j) a := sorry

end FiniteType

end Ring.DirectLimit.Algebra.Approximation
