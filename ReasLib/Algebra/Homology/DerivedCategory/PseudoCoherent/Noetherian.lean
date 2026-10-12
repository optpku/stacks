/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Noetherian homology criteria for pseudo-coherence

@stack 066E

Over a Noetherian ring, the bounded-above finite-homology description is the natural derived
category interface for pseudo-coherence.  The final module statement is kept unbundled so it can
be used without choosing a category presentation.
-/

open CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u v

namespace CategoryTheory.DerivedCategory.IsMPseudoCoherent

variable {R : Type u} [Ring R] [IsNoetherianRing R]

/-- Lemma 15.65.17 (1): `m`-pseudo-coherence is bounded above with finite homology in degrees
`≥ m`. -/
@[stacks 066E "m-pseudo-coherence over a Noetherian ring"]
theorem iff_boundedAbove_and_homology_finite_ge
    (K : DerivedCategory (ModuleCat.{v, u} R)) (m : ℤ) :
    K.IsMPseudoCoherent m ↔
      (t.minus : ObjectProperty (DerivedCategory (ModuleCat.{v, u} R))) K ∧
        ∀ i : ℤ, m ≤ i →
          Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v, u} R) i).obj K) := sorry
-- Proof strategy: compare with a bounded finite-free approximation for the forward implication;
-- conversely apply the bounded-above homology criterion after using Noetherianity to make every
-- finite homology module pseudo-coherent in the required shifted degree.

end CategoryTheory.DerivedCategory.IsMPseudoCoherent

namespace CategoryTheory.DerivedCategory.IsPseudoCoherent

variable {R : Type u} [Ring R] [IsNoetherianRing R]

/-- Lemma 15.65.17 (2): pseudo-coherence over a Noetherian ring is bounded above with finite
homology in every degree. -/
@[stacks 066E "pseudo-coherence over a Noetherian ring"]
theorem iff_boundedAbove_and_homology_finite
    (K : DerivedCategory (ModuleCat.{v, u} R)) :
    K.IsPseudoCoherent ↔
      (t.minus : ObjectProperty (DerivedCategory (ModuleCat.{v, u} R))) K ∧
        ∀ i : ℤ,
          Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v, u} R) i).obj K) := sorry
-- Proof strategy: apply the `m`-pseudo-coherent criterion in every degree and use the canonical
-- all-degree characterization of pseudo-coherence.

end CategoryTheory.DerivedCategory.IsPseudoCoherent

namespace Module

variable {R : Type u} [Ring R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Lemma 15.65.17 (3): a module over a Noetherian ring is pseudo-coherent exactly when it is
finite. -/
@[stacks 066E "Noetherian pseudo-coherent modules"]
theorem isPseudoCoherent_iff_finite :
    (ModuleCat.of R M).IsPseudoCoherent ↔ Module.Finite R M := sorry
-- Proof strategy: a finite module admits a bounded-above finite-free resolution over a
-- Noetherian ring; in the reverse direction, take degree-zero homology of a pseudo-coherent
-- representative and use finiteness of homology of a termwise finite-free complex.

end Module
