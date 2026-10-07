module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Sober
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Unibranch
public import stacks_project.Chap62.Lemma_62_6_6_Relative
public import stacks_project.Chap62.Lemma_62_8_2_Effective
public import stacks_project.Chap62.Remark_62_8_9_ClosedSubscheme

/-!
# Effective relative cycles from closed subschemes over a geometrically unibranch base
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Scheme.Hom TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- If `Z ⟶ S` has relative dimension at most `r`, then every scheme-theoretic
fibre of `Z` in `X_s` has topological Krull dimension at most `r`. -/
theorem fiberClosedSubschemeDimensionLE_of_morphismRelativeDimensionLE
    {X S : Scheme.{u}} (f : X ⟶ S) (Z : X.IdealSheafData) (r : ℕ)
    [RelativeDimensionLE (Z.subschemeι ≫ f) r] :
    f.fiberClosedSubschemeDimensionLE Z r := sorry

/-- Remark 62.8.9: if `f : X ⟶ S` is of finite type, `S` is Noetherian and
geometrically unibranch, `r ≥ 0`, and a closed subscheme `Z ⊂ X` has
`Z ⟶ S` of relative dimension `≤ r`, then for all sufficiently divisible
integers `n ≥ 1` there exists a unique effective relative `r`-cycle `α` on
`X / S` such that `α η = n • [Z_η]_r` for every generic point `η` of `S`.
This is a reformulation of Theorem 3.4.2 of Suslin–Voevodsky. -/
@[stacks 0H5Z]
theorem existsUnique_effective_of_genericClosedSubscheme
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S]
    (h_unibranch : S.isGeometricallyUnibranch) [f.FiniteType] (r : ℕ)
    (Z : X.IdealSheafData)
    [RelativeDimensionLE (Z.subschemeι ≫ f) r] :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ∣ n → 0 < n →
      ∃! α : Family f r, IsRelative α ∧ IsEffective α ∧
        ∀ η ∈ genericPoints S,
          α η = n • closedSubschemeFiber f Z r
            (fiberClosedSubschemeDimensionLE_of_morphismRelativeDimensionLE f Z r) η :=
  sorry

end AlgebraicGeometry.RelativeCycle
