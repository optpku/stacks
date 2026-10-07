module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Remark_87_28_1_Universal_property_restricted_power_series_RestrictedPowerSeries

@[expose] public section

universe u v w

open RestrictedPowerSeries

/-- Remark 87.28.1 (Universal property restricted power series): if `A → C` is a continuous
map of complete linearly topologized rings, then any `A`-algebra map
`A[x₁, …, xᵣ] → C` extends uniquely to a continuous map `A{x₁, …, xᵣ} → C` on
restricted power series. Here `A{x₁, …, xᵣ}` is `RestrictedPowerSeries (Fin r) A`, the
inverse limit of `(A ⧸ I)[σ]` over open ideals `I`, with the limit topology. -/
@[stacks 0AJM]
theorem RestrictedPowerSeries.existsUnique_continuousAlgHom
    {σ : Type u} {A : Type v} {C : Type w}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C] [T2Space C]
    [@CompleteSpace C (IsTopologicalAddGroup.rightUniformSpace C)]
    [Algebra A C] [ContinuousSMul A C] (φ : MvPolynomial σ A →ₐ[A] C) :
    ∃! ψ : RestrictedPowerSeries σ A →A[A] C, ψ.toAlgHom.comp ofPolynomial = φ :=
  sorry
