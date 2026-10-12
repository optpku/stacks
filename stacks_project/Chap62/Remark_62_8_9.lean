/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RelativeCycle.ClosedSubscheme

/-!
# Effective relative cycles from closed subschemes over a geometrically unibranch base
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Scheme.Hom TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/- Remark 62.8.9: if `f : X ⟶ S` is of finite type, `S` is Noetherian and
geometrically unibranch, `r ≥ 0`, and a closed subscheme `Z ⊂ X` has
`Z ⟶ S` of relative dimension `≤ r`, then for all sufficiently divisible
integers `n ≥ 1` there exists a unique effective relative `r`-cycle `α` on
`X / S` such that `α η = n • [Z_η]_r` for every generic point `η` of `S`.
This is a reformulation of Theorem 3.4.2 of Suslin–Voevodsky. -/
@[stacks 0H5Z] #check
  (AlgebraicGeometry.RelativeCycle.existsUnique_effective_of_genericClosedSubscheme :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S]
    (h_unibranch : S.isGeometricallyUnibranch) [f.FiniteType] (r : ℕ)
    (Z : X.IdealSheafData)
    [RelativeDimensionLE (Z.subschemeι ≫ f) r],
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ∣ n → 0 < n →
      ∃! α : f.FiberCycleFamily (r : ℤ), IsRelative α ∧ IsEffective α ∧
        ∀ η ∈ genericPoints S,
          α η = n • f.closedSubschemeFiberCycleFamily Z r
            (f.fiberClosedSubschemeDimensionLE_of_relativeDimensionLE Z r inferInstance) η)

end AlgebraicGeometry.RelativeCycle
