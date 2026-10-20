/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Order.DirectLimit.Reindex
public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Core maps for reindexed ring direct limits

An explicit order isomorphism gives canonical maps between the original and
reindexed direct limits.  This leaf owns those maps, their compatibility
conditions, and the resulting ring equivalence.
-/

@[expose] public section

universe u v w

noncomputable section

namespace Ring.DirectLimit.Reindex

variable {I : Type u} {J : Type v} [Preorder I] [Preorder J]
variable {G : I → Type w} [∀ i, CommRing (G i)]

/-- The canonical stage equivalence used when a source index is written as
`e (e.symm i)`. -/
noncomputable def stageEquiv (e : J ≃o I) (i : I) :
    G i ≃+* G (e (e.symm i)) :=
  (RingEquiv.cast (e.apply_symm_apply i)).symm

/-- The compatibility of the canonical maps from a reindexed stage to the
original direct limit. -/
theorem toFull_compatible (e : J ≃o I) (f : ∀ i j, i ≤ j → G i →+* G j)
    {j k : J} (h : j ≤ k) (x : G (e j)) :
    Ring.DirectLimit.of G (fun i j h ↦ f i j h) (e k)
        (f (e j) (e k) (e.monotone h) x) =
      Ring.DirectLimit.of G (fun i j h ↦ f i j h) (e j) x := sorry

/-- The map from the direct limit of a reindexed system back to the original
direct limit. -/
noncomputable def toFull (e : J ≃o I) (f : ∀ i j, i ≤ j → G i →+* G j) :
    Ring.DirectLimit (fun j : J ↦ G (e j))
        (fun j k h ↦ f (e j) (e k) (e.monotone h)) →+*
      Ring.DirectLimit G (fun i j h ↦ f i j h) :=
  Ring.DirectLimit.lift
    (fun j : J ↦ G (e j))
    (fun j k h ↦ f (e j) (e k) (e.monotone h))
    (Ring.DirectLimit G (fun i j h ↦ f i j h))
    (fun j ↦ Ring.DirectLimit.of G (fun i j h ↦ f i j h) (e j))
    (fun _ _ h x ↦ toFull_compatible e f h x)

/-- The compatibility of the inverse stage maps, with the equality of indices
encapsulated by `stageEquiv`. -/
theorem fromFull_compatible (e : J ≃o I) (f : ∀ i j, i ≤ j → G i →+* G j)
    {i k : I} (h : i ≤ k) (x : G i) :
    ((Ring.DirectLimit.of (fun j : J ↦ G (e j))
          (fun j k h ↦ f (e j) (e k) (e.monotone h)) (e.symm k)).comp
        (stageEquiv e k).toRingHom)
        (f i k h x) =
      ((Ring.DirectLimit.of (fun j : J ↦ G (e j))
          (fun j k h ↦ f (e j) (e k) (e.monotone h)) (e.symm i)).comp
        (stageEquiv e i).toRingHom) x := sorry

/-- The map from the original direct limit to the direct limit of the
reindexed system. -/
noncomputable def fromFull (e : J ≃o I) (f : ∀ i j, i ≤ j → G i →+* G j) :
    Ring.DirectLimit G (fun i j h ↦ f i j h) →+*
      Ring.DirectLimit (fun j : J ↦ G (e j))
        (fun j k h ↦ f (e j) (e k) (e.monotone h)) :=
  Ring.DirectLimit.lift
    G (fun i j h ↦ f i j h)
    (Ring.DirectLimit (fun j : J ↦ G (e j))
      (fun j k h ↦ f (e j) (e k) (e.monotone h)))
    (fun i ↦
      (Ring.DirectLimit.of (fun j : J ↦ G (e j))
        (fun j k h ↦ f (e j) (e k) (e.monotone h)) (e.symm i)).comp
        (stageEquiv e i).toRingHom)
    (fun _ _ h x ↦ fromFull_compatible e f h x)

/-- The two reindexing maps compose to the identity on the original direct
limit. -/
theorem toFull_comp_fromFull (e : J ≃o I) (f : ∀ i j, i ≤ j → G i →+* G j) :
    (toFull e f).comp (fromFull e f) = RingHom.id _ := sorry

/-- The two reindexing maps compose to the identity on the reindexed direct
limit. -/
theorem fromFull_comp_toFull (e : J ≃o I) (f : ∀ i j, i ≤ j → G i →+* G j) :
    (fromFull e f).comp (toFull e f) = RingHom.id _ := sorry

/-- The ring equivalence induced by reindexing along `e : J ≃o I`. -/
noncomputable def equiv (e : J ≃o I) (f : ∀ i j, i ≤ j → G i →+* G j) :
    Ring.DirectLimit (fun j : J ↦ G (e j))
        (fun j k h ↦ f (e j) (e k) (e.monotone h)) ≃+*
      Ring.DirectLimit G (fun i j h ↦ f i j h) :=
  RingEquiv.ofRingHom (toFull e f) (fromFull e f)
    (toFull_comp_fromFull e f) (fromFull_comp_toFull e f)

end Ring.DirectLimit.Reindex
