module

public import ReasLib.RingTheory.DirectLimit.Reindex.Core
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Computation laws for reindexed ring direct limits

This leaf exposes generator formulas and underlying-hom formulas for the
reindexing equivalence.  It is independent from applications that only need
the core comparison maps.
-/

@[expose] public section

universe u v w

noncomputable section

namespace Ring.DirectLimit.Reindex

variable {I : Type u} {J : Type v} [Preorder I] [Preorder J]
variable {G : I → Type w} [∀ i, CommRing (G i)]

/-- The forward reindexing map sends a generator to the corresponding
generator in the original presentation. -/
@[simp]
theorem toFull_of (e : J ≃o I) (f : ∀ i j, i ≤ j → G i →+* G j)
    (j : J) (x : G (e j)) :
    toFull e f
        (Ring.DirectLimit.of (fun j : J ↦ G (e j))
          (fun j k h ↦ f (e j) (e k) (e.monotone h)) j x) =
      Ring.DirectLimit.of G (fun i j h ↦ f i j h) (e j) x := sorry

/-- The inverse reindexing map sends a generator in the `e j` stage back to
the generator at `j`. -/
@[simp]
theorem fromFull_of (e : J ≃o I) (f : ∀ i j, i ≤ j → G i →+* G j)
    (j : J) (x : G (e j)) :
    fromFull e f
        (Ring.DirectLimit.of G (fun i j h ↦ f i j h) (e j) x) =
      Ring.DirectLimit.of (fun j : J ↦ G (e j))
        (fun j k h ↦ f (e j) (e k) (e.monotone h)) j x := sorry

/-- Evaluation of the forward reindexing equivalence is its canonical forward
ring homomorphism. -/
@[simp]
theorem equiv_apply (e : J ≃o I) (f : ∀ i j, i ≤ j → G i →+* G j)
    (x : Ring.DirectLimit (fun j : J ↦ G (e j))
      (fun j k h ↦ f (e j) (e k) (e.monotone h))) :
    equiv e f x = toFull e f x := sorry

/-- The reindexing equivalence sends a reindexed generator to the corresponding
generator in the original presentation. -/
@[simp]
theorem equiv_of (e : J ≃o I) (f : ∀ i j, i ≤ j → G i →+* G j)
    (j : J) (x : G (e j)) :
    equiv e f
        (Ring.DirectLimit.of (fun j : J ↦ G (e j))
          (fun j k h ↦ f (e j) (e k) (e.monotone h)) j x) =
      Ring.DirectLimit.of G (fun i j h ↦ f i j h) (e j) x := sorry

/-- The forward reindexing equivalence has `toFull` as its underlying ring
homomorphism. -/
theorem equiv_toRingHom (e : J ≃o I) (f : ∀ i j, i ≤ j → G i →+* G j) :
    (equiv e f).toRingHom = toFull e f := sorry

/-- The inverse reindexing equivalence has `fromFull` as its underlying ring
homomorphism. -/
theorem equiv_symm_toRingHom (e : J ≃o I) (f : ∀ i j, i ≤ j → G i →+* G j) :
    (equiv e f).symm.toRingHom = fromFull e f := sorry

/-- The inverse reindexing equivalence evaluates through `fromFull` on every
element of the original direct limit. -/
@[simp]
theorem equiv_symm_apply (e : J ≃o I) (f : ∀ i j, i ≤ j → G i →+* G j)
    (x : Ring.DirectLimit G (fun i j h ↦ f i j h)) :
    (equiv e f).symm x = fromFull e f x := sorry

/-- The inverse reindexing map evaluates on a generator at any original index,
with the canonical stage cast made explicit. -/
@[simp]
theorem fromFull_of_index (e : J ≃o I) (f : ∀ i j, i ≤ j → G i →+* G j)
    (i : I) (x : G i) :
    fromFull e f
        (Ring.DirectLimit.of G (fun i j h ↦ f i j h) i x) =
      Ring.DirectLimit.of (fun j : J ↦ G (e j))
        (fun j k h ↦ f (e j) (e k) (e.monotone h)) (e.symm i)
        ((stageEquiv e i).toRingHom x) := sorry

/-- The inverse equivalence sends a generator in the `e j` stage back to the
corresponding reindexed generator. -/
@[simp]
theorem equiv_symm_apply_of (e : J ≃o I) (f : ∀ i j, i ≤ j → G i →+* G j)
    (j : J) (x : G (e j)) :
    (equiv e f).symm
        (Ring.DirectLimit.of G (fun i j h ↦ f i j h) (e j) x) =
      Ring.DirectLimit.of (fun j : J ↦ G (e j))
        (fun j k h ↦ f (e j) (e k) (e.monotone h)) j x := sorry

/-- The inverse equivalence evaluates on a generator at any original index. -/
@[simp]
theorem equiv_symm_apply_of_index (e : J ≃o I)
    (f : ∀ i j, i ≤ j → G i →+* G j) (i : I) (x : G i) :
    (equiv e f).symm
        (Ring.DirectLimit.of G (fun i j h ↦ f i j h) i x) =
      Ring.DirectLimit.of (fun j : J ↦ G (e j))
        (fun j k h ↦ f (e j) (e k) (e.monotone h)) (e.symm i)
        ((stageEquiv e i).toRingHom x) := sorry

end Ring.DirectLimit.Reindex
