/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Topology.MinimalSpecialization
import StacksCheckRecall

@[expose] public section

open Set TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

section

variable (S : Scheme.{u})

#check
  (AlgebraicGeometry.Scheme.minimalSpecializationPoints (S := S) : Set S → Set S)

#check
  (AlgebraicGeometry.Scheme.mem_minimalSpecializationPoints_iff (S := S) :
    ∀ {T : Set S} {t : S},
      t ∈ S.minimalSpecializationPoints T ↔
        t ∈ T ∧ ∀ ⦃t' : S⦄, t' ∈ T → t' ⤳ t → t' = t)

#check
  (AlgebraicGeometry.Scheme.minimalSpecializationPoints.subset (S := S) :
    ∀ T : Set S, S.minimalSpecializationPoints T ⊆ T)

#check
  (AlgebraicGeometry.Scheme.minimalSpecializationPoints.eq_of_mem_of_specializes (S := S) :
    ∀ {T : Set S} {t t' : S},
      t ∈ S.minimalSpecializationPoints T → t' ∈ T → t' ⤳ t → t' = t)

/- Lemma 28.5.12 (1): specializations among the minimal specialization points of `T` are
trivial. -/
@[stacks 0G2R] #check
  (AlgebraicGeometry.Scheme.minimalSpecializationPoints.eq_of_specializes (S := S) :
    ∀ {T : Set S} {t₁ t₂ : S},
      t₁ ∈ S.minimalSpecializationPoints T →
        t₂ ∈ S.minimalSpecializationPoints T → t₁ ⤳ t₂ → t₁ = t₂)

/- Lemma 28.5.12 (2): every point of `T` is a specialization of a minimal specialization point
of `T`. -/
@[stacks 0G2R] #check
  (AlgebraicGeometry.Scheme.exists_mem_minimalSpecializationPoints_specializingTo (S := S) :
    ∀ [AlgebraicGeometry.IsNoetherian S] {T : Set S} {t : S},
      t ∈ T → ∃ t₀ ∈ S.minimalSpecializationPoints T, t₀ ⤳ t)

/- Lemma 28.5.12 (3): the closure of `T` equals the closure of its minimal specialization
points. -/
@[stacks 0G2R] #check
  (AlgebraicGeometry.Scheme.closure_eq_closure_minimalSpecializationPoints (S := S) :
    ∀ [AlgebraicGeometry.IsNoetherian S] {T : Set S},
      closure T = closure (S.minimalSpecializationPoints T))

end

end AlgebraicGeometry.Scheme
