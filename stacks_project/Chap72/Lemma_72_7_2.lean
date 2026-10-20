/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.LocallyFinite
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap72.Definition_72_4_1_Integral
public import stacks_project.Chap72.Lemma_72_7_2_Pullback

/-!
# Local finiteness of prime divisors of a regular meromorphic section

On a locally Noetherian integral algebraic space, the prime divisors at which a
regular meromorphic section of an invertible module fails to lie in `L_ξ`, and
those along which its order is nonzero, form locally finite families in
`Points X`. Here `L_ξ = (Modules.pullback (fromHenselization X ξ)).obj L`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
variable [IsLocallyNoetherian X] [IsIntegral X]

/-- Lemma 72.7.2 (1): Let `S` be a scheme. Let `X` be a locally Noetherian
integral algebraic space over `S`. Let `L` be an invertible `𝒪_X`-module.
Let `s ∈ Γ(X, 𝒦_X(L))` be a regular (i.e., nonzero) meromorphic section of `L`.
Then the family of prime divisors `Z` with generic point `ξ` such that `s` is
not in `L_ξ` is locally finite in `Points X`, where
`L_ξ = (Modules.pullback (fromHenselization X ξ)).obj L`. -/
@[stacks 0EPS]
theorem locallyFinite_primeDivisors_regularMeromorphicSection_not_regularAt
    {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      {x | ¬ MeromorphicSection.IsRegularAt s Z.genericPoint ∧ x ∈ Z.pointsSet} :=
  sorry

/-- Lemma 72.7.2 (2): Let `S` be a scheme. Let `X` be a locally Noetherian
integral algebraic space over `S`. Let `L` be an invertible `𝒪_X`-module.
Let `s ∈ Γ(X, 𝒦_X(L))` be a regular (i.e., nonzero) meromorphic section of `L`.
Then the family of prime divisors `Z` with `ord_{Z, L}(s) ≠ 0` is locally
finite in `Points X`. Nonzero-order supports are encoded as
`if ord s hs Z = 0 then ∅ else Z.pointsSet`. -/
@[stacks 0EPS]
theorem locallyFinite_regularMeromorphicSectionOrder_ne_zero
    {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      if MeromorphicSection.ord s hs Z = 0 then (∅ : Set (Points X)) else Z.pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
