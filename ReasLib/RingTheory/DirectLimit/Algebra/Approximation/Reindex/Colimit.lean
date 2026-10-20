/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Colimit
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Reindex.Core
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Colimits of reindexed directed algebra approximations

This leaf records how the chosen source and target colimit identifications,
and the map induced on colimits, behave after an order-isomorphic reindexing.
-/

@[expose] public section

universe u v w x

noncomputable section

namespace Ring.DirectLimit.Algebra.Approximation.Hom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/-- The source colimit equivalence of a reindexed approximation is the
generic reindexing equivalence followed by the original identification. -/
@[stacks 00R1 "reindexed directed approximation colimit"]
theorem reindex_sourceColimit (A : Hom f) {J : Type x}
    [Preorder J] (e : J ≃o A.index) :
    (A.reindex e).sourceColimit =
      (Ring.DirectLimit.Reindex.equiv e
        (fun i j h ↦ A.sourceMap i j h)).trans A.sourceColimit := sorry

/-- The target colimit equivalence of a reindexed approximation is the
generic reindexing equivalence followed by the original identification. -/
@[stacks 00R1 "reindexed directed approximation colimit"]
theorem reindex_targetColimit (A : Hom f) {J : Type x}
    [Preorder J] (e : J ≃o A.index) :
    (A.reindex e).targetColimit =
      (Ring.DirectLimit.Reindex.equiv e
        (fun i j h ↦ A.targetMap i j h)).trans A.targetColimit := sorry

/-- The source colimit identification evaluates by first returning to the
original direct-limit presentation. -/
@[simp, stacks 00R1 "reindexed directed approximation colimit"]
theorem reindex_sourceColimit_apply (A : Hom f) {J : Type x}
    [Preorder J] (e : J ≃o A.index)
    (a : Ring.DirectLimit (fun j : J ↦ A.source (e j))
      (fun j k h ↦ A.sourceMap (e j) (e k) (e.monotone h))) :
    (A.reindex e).sourceColimit a =
      A.sourceColimit (Ring.DirectLimit.Reindex.toFull e
        (fun i j h ↦ A.sourceMap i j h) a) := sorry

/-- The target colimit identification evaluates by first returning to the
original direct-limit presentation. -/
@[simp, stacks 00R1 "reindexed directed approximation colimit"]
theorem reindex_targetColimit_apply (A : Hom f) {J : Type x}
    [Preorder J] (e : J ≃o A.index)
    (b : Ring.DirectLimit (fun j : J ↦ A.target (e j))
      (fun j k h ↦ A.targetMap (e j) (e k) (e.monotone h))) :
    (A.reindex e).targetColimit b =
      A.targetColimit (Ring.DirectLimit.Reindex.toFull e
        (fun i j h ↦ A.targetMap i j h) b) := sorry

/-- The source colimit identification sends a reindexed generator to the
same element as the corresponding original generator. -/
@[simp, stacks 00R1 "reindexed directed approximation colimit"]
theorem reindex_sourceColimit_of (A : Hom f) {J : Type x}
    [Preorder J] (e : J ≃o A.index) (j : J) (a : A.source (e j)) :
    (A.reindex e).sourceColimit
        (Ring.DirectLimit.of (fun j : J ↦ A.source (e j))
          (fun j k h ↦ A.sourceMap (e j) (e k) (e.monotone h)) j a) =
      A.sourceColimit
        (Ring.DirectLimit.of A.source
          (fun i k h ↦ A.sourceMap i k h) (e j) a) := sorry

/-- The target colimit identification sends a reindexed generator to the
same element as the corresponding original generator. -/
@[simp, stacks 00R1 "reindexed directed approximation colimit"]
theorem reindex_targetColimit_of (A : Hom f) {J : Type x}
    [Preorder J] (e : J ≃o A.index) (j : J) (b : A.target (e j)) :
    (A.reindex e).targetColimit
        (Ring.DirectLimit.of (fun j : J ↦ A.target (e j))
          (fun j k h ↦ A.targetMap (e j) (e k) (e.monotone h)) j b) =
      A.targetColimit
        (Ring.DirectLimit.of A.target
          (fun i k h ↦ A.targetMap i k h) (e j) b) := sorry

/-- The source-stage map to the limit is unchanged by reindexing. -/
@[stacks 00R1 "reindexed directed approximation colimit"]
theorem reindex_sourceToLimit (A : Hom f) {J : Type x}
    [Preorder J] (e : J ≃o A.index) (j : J) :
    (A.reindex e).sourceToLimit j = A.sourceToLimit (e j) := sorry

/-- The target-stage map to the limit is unchanged by reindexing. -/
@[stacks 00R1 "reindexed directed approximation colimit"]
theorem reindex_targetToLimit (A : Hom f) {J : Type x}
    [Preorder J] (e : J ≃o A.index) (j : J) :
    (A.reindex e).targetToLimit j = A.targetToLimit (e j) := sorry

/-- Reindexed source-stage maps to the limit agree pointwise with the
original stage maps. -/
@[simp, stacks 00R1 "reindexed directed approximation colimit"]
theorem reindex_sourceToLimit_apply (A : Hom f) {J : Type x}
    [Preorder J] (e : J ≃o A.index) (j : J) (a : A.source (e j)) :
    (A.reindex e).sourceToLimit j a = A.sourceToLimit (e j) a := sorry

/-- Reindexed target-stage maps to the limit agree pointwise with the
original stage maps. -/
@[simp, stacks 00R1 "reindexed directed approximation colimit"]
theorem reindex_targetToLimit_apply (A : Hom f) {J : Type x}
    [Preorder J] (e : J ≃o A.index) (j : J) (b : A.target (e j)) :
    (A.reindex e).targetToLimit j b = A.targetToLimit (e j) b := sorry

/-- The colimit map of a reindexed approximation commutes with the canonical
maps from the reindexed source and target direct limits to the original ones. -/
@[stacks 00R1 "reindexed directed approximation colimit"]
theorem reindex_colimitMap_naturality (A : Hom f) {J : Type x}
    [Preorder J] (e : J ≃o A.index) :
    (Ring.DirectLimit.Reindex.toFull e
        (fun i j h ↦ A.targetMap i j h)).comp
        ((A.reindex e).colimitMap) =
      A.colimitMap.comp
        (Ring.DirectLimit.Reindex.toFull e
          (fun i j h ↦ A.sourceMap i j h)) := sorry

/-- Pointwise form of the naturality square for a reindexed colimit map. -/
@[simp, stacks 00R1 "reindexed directed approximation colimit"]
theorem reindex_colimitMap_toFull (A : Hom f) {J : Type x}
    [Preorder J] (e : J ≃o A.index)
    (x : Ring.DirectLimit (fun j : J ↦ A.source (e j))
      (fun j k h ↦ A.sourceMap (e j) (e k) (e.monotone h))) :
    Ring.DirectLimit.Reindex.toFull e
        (fun i j h ↦ A.targetMap i j h)
        ((A.reindex e).colimitMap x) =
      A.colimitMap
        (Ring.DirectLimit.Reindex.toFull e
          (fun i j h ↦ A.sourceMap i j h) x) := sorry

end Ring.DirectLimit.Algebra.Approximation.Hom
