/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.CategoryTheory.Filtration.Indexed

/-!
# Cartier-rank filtrations of scheme modules

This module packages paired locally finite filtrations whose corresponding
graded pieces come from finite locally free modules on a common sequence of
effective Cartier divisors.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ModuleRestriction ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {E : X.Modules}

/-- Paired increasing and decreasing filtrations of a scheme module whose matching
successive quotients are pushforwards of rank-`n + 1` modules on the same effective
Cartier divisor. The stage `ascending n` represents `F^n`, while `descending.stage n`
represents `F_{n+1}`. -/
structure CartierRankFiltrations (E : X.Modules) where
  /-- The increasing filtration `F^0 ⊆ F^1 ⊆ ⋯`. -/
  ascending : ℕ →o Subobject E
  /-- The decreasing filtration `F_1 ⊇ F_2 ⊇ ⋯`. -/
  descending : IndexedFiltration ℕ E
  /-- The increasing filtration begins with the zero subobject. -/
  ascending_zero : ascending 0 = ⊥
  /-- The decreasing filtration begins with the whole module. -/
  descending_zero : descending.stage 0 = ⊤
  /-- Locally around every point, all sufficiently late increasing stages equal the
  whole module. -/
  ascending_locally_eventually_top :
    ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (N : ℕ),
      ∀ n : ℕ, N ≤ n → IsIso ((ascending n).arrow |_ U)
  /-- Locally around every point, all sufficiently late decreasing stages vanish. -/
  descending_locally_eventually_bot :
    ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (N : ℕ),
      ∀ n : ℕ, N ≤ n → IsZero ((descending.stage n : X.Modules).over U)
  /-- The effective Cartier divisor supporting the two rank-`n + 1` graded pieces. -/
  divisor : ℕ → X.IdealSheafData
  /-- Each member of `divisor` defines an effective Cartier divisor. -/
  divisor_isEffective :
    ∀ n : ℕ, IsEffectiveCartierDivisor (divisor n).subschemeι
  /-- A module on `divisor n` whose pushforward is the increasing graded piece. -/
  ascendingPiece : (n : ℕ) → (divisor n).subscheme.Modules
  /-- A module on `divisor n` whose pushforward is the decreasing graded piece. -/
  descendingPiece : (n : ℕ) → (divisor n).subscheme.Modules
  /-- The increasing divisor-side piece has rank `n + 1`. -/
  ascendingPiece_rank :
    ∀ n : ℕ, IsFiniteLocallyFreeOfRank (n + 1) (ascendingPiece n)
  /-- The decreasing divisor-side piece has rank `n + 1`. -/
  descendingPiece_rank :
    ∀ n : ℕ, IsFiniteLocallyFreeOfRank (n + 1) (descendingPiece n)
  /-- The increasing successive quotient is the pushforward of its divisor-side piece. -/
  ascendingPieceIso (n : ℕ) :
    cokernel (Subobject.ofLE (ascending n) (ascending (n + 1))
      (ascending.monotone (Nat.le_succ n))) ≅
        (pushforward (divisor n).subschemeι).obj (ascendingPiece n)
  /-- The decreasing successive quotient is the pushforward of its divisor-side piece. -/
  descendingPieceIso (n : ℕ) :
    cokernel (descending.inclusion (Nat.le_succ n)) ≅
      (pushforward (divisor n).subschemeι).obj (descendingPiece n)

namespace CartierRankFiltrations

/-- Assemble paired Cartier-rank filtrations from their stages, supporting divisors,
divisor-side modules, quotient identifications, and proof-valued conditions. -/
def ofStages (ascending : ℕ →o Subobject E) (descending : IndexedFiltration ℕ E)
    (ascending_zero : ascending 0 = ⊥) (descending_zero : descending.stage 0 = ⊤)
    (ascending_locally_eventually_top :
      ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (N : ℕ),
        ∀ n : ℕ, N ≤ n → IsIso ((ascending n).arrow |_ U))
    (descending_locally_eventually_bot :
      ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (N : ℕ),
        ∀ n : ℕ, N ≤ n → IsZero ((descending.stage n : X.Modules).over U))
    (divisor : ℕ → X.IdealSheafData)
    (divisor_isEffective : ∀ n : ℕ, IsEffectiveCartierDivisor (divisor n).subschemeι)
    (ascendingPiece : (n : ℕ) → (divisor n).subscheme.Modules)
    (descendingPiece : (n : ℕ) → (divisor n).subscheme.Modules)
    (ascendingPiece_rank :
      ∀ n : ℕ, IsFiniteLocallyFreeOfRank (n + 1) (ascendingPiece n))
    (descendingPiece_rank :
      ∀ n : ℕ, IsFiniteLocallyFreeOfRank (n + 1) (descendingPiece n))
    (ascendingPieceIso : (n : ℕ) →
      cokernel (Subobject.ofLE (ascending n) (ascending (n + 1))
        (ascending.monotone (Nat.le_succ n))) ≅
          (pushforward (divisor n).subschemeι).obj (ascendingPiece n))
    (descendingPieceIso : (n : ℕ) →
      cokernel (descending.inclusion (Nat.le_succ n)) ≅
        (pushforward (divisor n).subschemeι).obj (descendingPiece n)) :
    CartierRankFiltrations E where
  ascending := ascending
  descending := descending
  ascending_zero := ascending_zero
  descending_zero := descending_zero
  ascending_locally_eventually_top := ascending_locally_eventually_top
  descending_locally_eventually_bot := descending_locally_eventually_bot
  divisor := divisor
  divisor_isEffective := divisor_isEffective
  ascendingPiece := ascendingPiece
  descendingPiece := descendingPiece
  ascendingPiece_rank := ascendingPiece_rank
  descendingPiece_rank := descendingPiece_rank
  ascendingPieceIso := ascendingPieceIso
  descendingPieceIso := descendingPieceIso

/-- The `n`-th increasing graded piece, defined as the cokernel of
`F^n ⟶ F^(n+1)`. -/
noncomputable def ascendingQuotient (G : CartierRankFiltrations E) (n : ℕ) : X.Modules :=
  cokernel (Subobject.ofLE (G.ascending n) (G.ascending (n + 1))
    (G.ascending.monotone (Nat.le_succ n)))

/-- The `n`-th decreasing graded piece, defined as the cokernel of
`F_(n+2) ⟶ F_(n+1)`. -/
noncomputable def descendingQuotient (G : CartierRankFiltrations E) (n : ℕ) : X.Modules :=
  cokernel (G.descending.inclusion (Nat.le_succ n))

/-- Identify the increasing graded piece with the pushforward of the corresponding
rank-`n + 1` module on its effective Cartier divisor. -/
noncomputable def ascendingQuotientIso (G : CartierRankFiltrations E) (n : ℕ) :
    G.ascendingQuotient n ≅
      (pushforward (G.divisor n).subschemeι).obj (G.ascendingPiece n) :=
  G.ascendingPieceIso n

/-- Identify the decreasing graded piece with the pushforward of the corresponding
rank-`n + 1` module on its effective Cartier divisor. -/
noncomputable def descendingQuotientIso (G : CartierRankFiltrations E) (n : ℕ) :
    G.descendingQuotient n ≅
      (pushforward (G.divisor n).subschemeι).obj (G.descendingPiece n) :=
  G.descendingPieceIso n

/-- The endpoint, local-finiteness, common effective-Cartier support, rank, and
quotient-identification properties carried by paired Cartier-rank filtrations. -/
theorem spec (G : CartierRankFiltrations E) :
    ((G.ascending 0 = ⊥ ∧ G.descending.stage 0 = ⊤) ∧
      ((∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (N : ℕ),
          ∀ n : ℕ, N ≤ n → IsIso ((G.ascending n).arrow |_ U)) ∧
        (∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (N : ℕ),
          ∀ n : ℕ, N ≤ n → IsZero ((G.descending.stage n : X.Modules).over U)))) ∧
      ∀ n : ℕ,
        IsEffectiveCartierDivisor (G.divisor n).subschemeι ∧
          IsFiniteLocallyFreeOfRank (n + 1) (G.ascendingPiece n) ∧
          IsFiniteLocallyFreeOfRank (n + 1) (G.descendingPiece n) ∧
          IsIso (G.ascendingQuotientIso n).hom ∧
          IsIso (G.descendingQuotientIso n).hom := sorry

end CartierRankFiltrations

end AlgebraicGeometry.Scheme.Modules
