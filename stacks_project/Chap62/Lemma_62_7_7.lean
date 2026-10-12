/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RelativeCycle.Weighting

/-!
# Weightings and relative 0-cycles

Relative 0-cycles on a locally quasi-finite morphism over a locally Noetherian
base determine integer weightings, and conversely every weighting has a positive
integer multiple equal to such a map when the source is quasi-compact.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/- Lemma 62.7.7 (1): if `S` is locally Noetherian and `f : X ⟶ S` is locally
quasi-finite, then for a relative 0-cycle `α` the map `weighting α` is a
weighting of `f`. -/
@[stacks 0H5P] #check (AlgebraicGeometry.RelativeCycle.isWeighting_weighting :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (α : f.FiberCycleFamily 0) (hα : IsRelative α),
    f.IsWeighting (weighting α))

/- Lemma 62.7.7 (2): if in addition `X` is quasi-compact, then every weighting
`w` of `f` satisfies `n • w = weighting α` for some positive integer `n` and
some relative 0-cycle `α`. -/
@[stacks 0H5P] #check (AlgebraicGeometry.RelativeCycle.exists_nsmul_eq_weighting :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [CompactSpace X] (w : X → ℤ) (hw : f.IsWeighting w),
    ∃ n : ℕ, 0 < n ∧ ∃ α : f.FiberCycleFamily 0,
      IsRelative α ∧ n • w = weighting α)

/- Lemma 62.7.7 (3): if moreover `S` is a scheme over `F_p` for a prime `p`,
then the integer in (2) may be taken to be a power of `p`. -/
@[stacks 0H5P] #check (AlgebraicGeometry.RelativeCycle.exists_pow_nsmul_eq_weighting :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [CompactSpace X] {p : ℕ} [Fact p.Prime] [S.IsCharP p]
    (w : X → ℤ) (hw : f.IsWeighting w),
    ∃ k : ℕ, ∃ α : f.FiberCycleFamily 0,
      IsRelative α ∧ p ^ k • w = weighting α)

end AlgebraicGeometry.RelativeCycle
