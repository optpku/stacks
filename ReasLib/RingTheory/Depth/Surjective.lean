module

public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Depth
public import ReasLib.RingTheory.Sequence.Regularity

@[expose] public section

/-!
# Depth Under Surjective Scalar Maps

@stack 00LI

This leaf owns the scalar-restriction invariance of regular-sequence lengths
and depth along a surjective algebra map.  The ideal-level statements are
independent of locality; local depth is their maximal-ideal specialization.
-/

universe u v w

namespace Ideal

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- A list whose generated ideal lies in the image of `I` lifts through a
surjective scalar map to a list whose generated ideal lies in `I`. -/
@[stacks 00LI "lifting lists through a surjective scalar map"]
theorem ofList_le_map_iff_of_surjective
    (I : Ideal R) (xs : List S)
    (hsurj : Function.Surjective (algebraMap R S)) :
    Ideal.ofList xs ≤ I.map (algebraMap R S) ↔
      ∃ ys : List R, ys.map (algebraMap R S) = xs ∧ Ideal.ofList ys ≤ I := sorry

/-- Surjective restriction of scalars preserves regular-sequence lengths in an
ideal and its image. -/
@[stacks 00LI "regular-sequence lengths under a surjection"]
theorem regularSequenceLengths_map_eq_of_surjective
    (I : Ideal R) (hsurj : Function.Surjective (algebraMap R S)) :
    regularSequenceLengths I M =
      regularSequenceLengths (I.map (algebraMap R S)) M := sorry

/-- Surjective restriction of scalars preserves ideal depth. -/
@[stacks 00LI "ideal depth under a surjection"]
theorem depth_map_eq_of_surjective
    (I : Ideal R) (hsurj : Function.Surjective (algebraMap R S)) :
    depth I M = depth (I.map (algebraMap R S)) M := sorry

end Ideal

/-- A module over a surjective local algebra has the same local depth after
restricting scalars. -/
@[stacks 00LI "local module depth under a surjection"]
theorem moduleDepth_eq_of_surjective
    {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (hsurj : Function.Surjective (algebraMap R S)) :
    moduleDepth R M = moduleDepth S M := sorry
