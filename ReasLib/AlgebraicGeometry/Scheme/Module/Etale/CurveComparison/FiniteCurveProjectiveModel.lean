/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteQuotientComplexReplacement

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
noncomputable section
universe u v

namespace FiniteCurveProjectiveModel
variable (R : Type u) (G : Type v) [Ring R] [Finite R]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable (K : CochainComplex (DiscreteModuleCat R G) ℤ) [K.IsStrictlyGE 0]
variable [Finite (K.homology 0).obj.V] [Finite (K.homology 1).obj.V]
variable [Finite (K.homology 2).obj.V]

abbrev finiteModel := FiniteCurveComplexModel.finiteCochain R G K

instance finiteModel_finite (i : ℤ) : Finite ((finiteModel R G K).X i).obj.V :=
  FiniteCurveComplexModel.finite_terms R G K i

instance finiteModel_nonnegative : CochainComplex.IsStrictlyGE (finiteModel R G K) 0 := by sorry
instance finiteModel_upper : CochainComplex.IsStrictlyLE (finiteModel R G K) 2 := by sorry

/-- Finite quotient free replacement of the actual finite subcomplex of truncation. -/
abbrev complex := FiniteQuotientComplexReplacement.complex R G (finiteModel R G K)

/-- The explicit map into K: free compatible-pair projections, quotient recovery,
then actual inclusion of chosen cycles and boundary lifts. -/
def toOriginal : complex R G K ⟶ K :=
  FiniteQuotientComplexReplacement.toOriginal R G (finiteModel R G K) ≫
    FiniteCurveComplexModel.inclusion R G K

theorem toOriginal_quasiIso
    (hvan : ∀ i : ℤ, 2 < i → CategoryTheory.Limits.IsZero (K.homology i)) :
    QuasiIso (toOriginal R G K) := by
  -- Local instance justification (proof-local temporary data): this specified replacement is a quasi-isomorphism.
  letI := FiniteQuotientComplexReplacement.toOriginal_quasiIso R G (finiteModel R G K)
  -- Local instance justification (proof-local temporary data): the stated vanishing validates the specified inclusion.
  letI := FiniteCurveComplexModel.inclusion_quasiIso R G K hvan
  exact inferInstanceAs (QuasiIso
    (FiniteQuotientComplexReplacement.toOriginal R G (finiteModel R G K) ≫
      FiniteCurveComplexModel.inclusion R G K))

theorem term_finite (i : ℤ) : Finite ((complex R G K).X i).obj.V :=
  FiniteQuotientComplexReplacement.term_finite R G (finiteModel R G K) i

theorem term_projective (i : ℤ) : Module.Projective R ((complex R G K).X i).obj.V :=
  FiniteQuotientComplexReplacement.term_projective R G (finiteModel R G K) i

end FiniteCurveProjectiveModel
