/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finite morphisms over locally Noetherian bases

Over a locally Noetherian target, a morphism of schemes is finite if and only if it is
proper and has finite point-set fibres.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.IsFinite

/-- Lemma 30.21.1: let `f : X ⟶ S` be a morphism of schemes, and assume `S` is locally
Noetherian. Then `f` is finite if and only if `f` is proper and every fibre
`f ⁻¹' {s}` is finite. (A more general version is Lemma 37.44.1.) -/
@[stacks 02OG]
theorem iff_isProper_and_finiteFibers {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) :
    IsFinite f ↔ IsProper f ∧ ∀ s : S, Set.Finite (f ⁻¹' ({s} : Set S)) := sorry

end AlgebraicGeometry.IsFinite
