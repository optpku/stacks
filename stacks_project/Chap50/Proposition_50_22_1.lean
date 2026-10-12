/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap50.Proposition_50_22_1_WeilTheory
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory

noncomputable section

universe u y z

namespace AlgebraicGeometry.Scheme.DeRham

variable {k : Type u} [Field k] [CharZero k]
variable {V : Type (u + 1)} [Category.{z} V]
variable {dimension : V → ℕ} {product : V → V → V}
variable {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
variable {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
variable {pointCycle : CHgrade point 0}
variable {geometry : WeilCohomology.SmoothProjectiveContext k V dimension product fst snd
  point CH CHgrade cyclePullback cyclePushforward pointCycle}
variable {H : V → Type (u + 1)} [∀ X, Ring (H X)] [∀ X, Algebra k (H X)]

/-- Proposition 50.22.1: over a characteristic-zero field, the graded contravariant
de Rham cohomology functor on smooth projective schemes is a Weil cohomology theory. -/
@[stacks 0FWD]
theorem cohomologyIsWeil (deRham : PreWeilRealization geometry H) :
    -- Local instance justification (defeq pin): use the grading supplied by the canonical pre-Weil to classical-theory conversion.
    letI : ∀ X, GradedAlgebra (deRham.toPreWeilTheory.Hgrade X) := deRham.toPreWeilTheory.gradedAlgebraHgrade
    deRham.toClassicalTheory.IsWeil :=
  deRham.toPreWeilTheory.isWeil_of_axiomsA1ToA8 deRham.satisfiesAxiomA8

end AlgebraicGeometry.Scheme.DeRham
