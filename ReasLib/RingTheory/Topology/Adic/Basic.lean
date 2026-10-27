/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ideals of definition and pre-adic topological rings
-/

@[expose] public section

open scoped Topology

universe u

namespace TopologicalRing

section

variable {R : Type u} [CommRing R] [TopologicalSpace R]

namespace Ideal

/-- An ideal of definition is open and its powers are cofinal among neighborhoods of zero. -/
@[stacks 07E8 "(4), ideal of definition"]
def IsIdealOfDefinition (I : Ideal R) : Prop :=
  IsOpen (I : Set R) ∧ ∀ U ∈ 𝓝 (0 : R), ∃ n : ℕ, ((I ^ n : Ideal R) : Set R) ⊆ U

/-- An ideal is an ideal of definition exactly when it is open and its powers are cofinal at
zero. -/
theorem isIdealOfDefinition_iff (I : Ideal R) :
    IsIdealOfDefinition I ↔
      IsOpen (I : Set R) ∧
        ∀ U ∈ 𝓝 (0 : R), ∃ n : ℕ, ((I ^ n : Ideal R) : Set R) ⊆ U := Iff.rfl

/-- An ideal inducing the ambient adic topology is an ideal of definition. -/
theorem isIdealOfDefinition_of_isAdic [IsTopologicalRing R] {I : Ideal R} (hI : IsAdic I) :
    IsIdealOfDefinition I := sorry

namespace IsIdealOfDefinition

/-- Ideals of definition have cofinal positive powers. -/
theorem exists_pow_le {I J : Ideal R}
    (hI : IsIdealOfDefinition I) (hJ : IsIdealOfDefinition J) :
    ∃ k > 0, I ^ k ≤ J := sorry

end IsIdealOfDefinition

end Ideal

/-- A pre-admissible topological ring is linearly topologized and has an ideal of definition. -/
@[stacks 07E8 "(5), pre-admissible ring"]
class IsPreadmissibleRing (R : Type u) [CommRing R] [TopologicalSpace R] : Prop
    extends IsTopologicalRing R, IsLinearTopology R R where
  /-- A pre-admissible ring has an ideal of definition. -/
  exists_ideal_isIdealOfDefinition : ∃ I : Ideal R, Ideal.IsIdealOfDefinition I

/-- A pre-adic topological ring has a defining ideal whose adic topology is the ambient topology. -/
@[stacks 07E8 "(7), pre-adic ring"]
class IsPreadicRing (R : Type u) [CommRing R] [TopologicalSpace R] : Prop
    extends IsTopologicalRing R where
  /-- A pre-adic ring has an ideal defining the ambient adic topology. -/
  exists_ideal_isAdic : ∃ I : Ideal R, IsAdic I

/-- A pre-adic ring is pre-admissible after forgetting the chosen adic ideal. -/
instance instIsPreadmissibleRing [IsPreadicRing R] : IsPreadmissibleRing R := sorry

/-- In a pre-adic ring, every ideal of definition induces the ambient topology. -/
theorem Ideal.IsIdealOfDefinition.isAdic [IsPreadicRing R] {I : Ideal R}
    (hI : Ideal.IsIdealOfDefinition I) : IsAdic I := sorry

end

end TopologicalRing
