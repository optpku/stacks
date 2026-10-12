/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Extension.Cotangent.Surjective

/-!
# Conormal Maps of Formally Smooth Presentations

For a presentation `P : Algebra.Extension R S`, this leaf identifies the
canonical conormal module of a surjective base map with the left end of the
presentation cotangent complex.  The map, exactness, and endpoint properties
are exposed separately so users need not choose a short-complex packaging.
-/

@[expose] public section

namespace Algebra.Extension.Conormal

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Tag `06A9`: formal smoothness of a presentation identifies its first cotangent homology
with the canonical conormal module of a surjective `R`-algebra map to its target. -/
@[stacks 06A9 "conormal presentation homology equivalence"]
noncomputable def h1Equiv
    (P : Extension.{w} R S) [Algebra.FormallySmooth R P.Ring]
    (hRS : Function.Surjective (algebraMap R S)) :
    P.H1Cotangent ≃ₗ[S] (Extension.ofSurjective (Algebra.ofId R S) hRS).Cotangent :=
  P.equivH1CotangentOfFormallySmooth.trans (Algebra.H1Cotangent.equivOfSurjective hRS)

/-- Tag `06A9`: the conormal map obtained from a formally smooth presentation and a surjective
base map to its target. -/
@[stacks 06A9 "formally smooth presentation conormal map"]
noncomputable def map
    (P : Extension.{w} R S) [Algebra.FormallySmooth R P.Ring]
    (hRS : Function.Surjective (algebraMap R S)) :
    (Extension.ofSurjective (Algebra.ofId R S) hRS).Cotangent →ₗ[S] P.Cotangent :=
  P.h1Cotangentι ∘ₗ (h1Equiv P hRS).symm.toLinearMap

/-- Tag `06A9`: the cotangent-complex map annihilates the conormal map of a formally smooth
presentation. -/
@[stacks 06A9 "conormal map is a complex map"]
theorem cotangentComplex_comp_map_eq_zero
    (P : Extension.{w} R S) [Algebra.FormallySmooth R P.Ring]
    (hRS : Function.Surjective (algebraMap R S)) :
    P.cotangentComplex.comp (map P hRS) = 0 := sorry

/-- Tag `06A9`: the conormal map of a formally smooth presentation is injective. -/
@[stacks 06A9 "formally smooth presentation conormal injectivity"]
theorem map_injective
    (P : Extension.{w} R S) [Algebra.FormallySmooth R P.Ring]
    (hRS : Function.Surjective (algebraMap R S)) :
    Function.Injective (map P hRS) := sorry

/-- Tag `06A9`: the conormal map and cotangent-complex map are exact. -/
@[stacks 06A9 "formally smooth presentation conormal exactness"]
theorem exact_map_cotangentComplex
    (P : Extension.{w} R S) [Algebra.FormallySmooth R P.Ring]
    (hRS : Function.Surjective (algebraMap R S)) :
    Function.Exact (map P hRS) P.cotangentComplex := sorry

/-- Tag `06A9`: when the base map to the target is surjective, the cotangent-complex map of any
presentation is surjective. -/
@[stacks 06A9 "surjective presentation cotangent endpoint"]
theorem cotangentComplex_surjective
    (P : Extension.{w} R S) (hRS : Function.Surjective (algebraMap R S)) :
    Function.Surjective P.cotangentComplex := sorry

end Algebra.Extension.Conormal
