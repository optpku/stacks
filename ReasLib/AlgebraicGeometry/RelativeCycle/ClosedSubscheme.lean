/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Effective
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.Hilbert
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Unibranch

/-!
# Effective relative cycles associated to closed subschemes
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Scheme.Hom TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Over a Noetherian geometrically unibranch base, a closed subscheme of relative
dimension at most `r` in a finite-type scheme determines, for all sufficiently
divisible positive integers `n`, a unique effective relative `r`-cycle whose
generic fibres are `n` times the associated cycles of the closed subscheme. -/
theorem existsUnique_effective_of_genericClosedSubscheme
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S]
    (h_unibranch : S.isGeometricallyUnibranch) [f.FiniteType] (r : ℕ)
    (Z : X.IdealSheafData) [RelativeDimensionLE (Z.subschemeι ≫ f) r] :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ∣ n → 0 < n →
      ∃! α : f.FiberCycleFamily (r : ℤ), IsRelative α ∧ IsEffective α ∧
        ∀ η ∈ genericPoints S,
          α η = n • f.closedSubschemeFiberCycleFamily Z r
            (f.fiberClosedSubschemeDimensionLE_of_relativeDimensionLE Z r inferInstance) η := sorry

end AlgebraicGeometry.RelativeCycle
