module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RestrictedPowerSeries
import StacksCheckRecall

@[expose] public section

universe u v w

/- Remark 87.28.1 (Universal property restricted power series) -/
@[stacks 0AJM] #check (RestrictedPowerSeries.existsUnique_continuousAlgHom :
    ∀ {r : ℕ} {A : Type v} {C : Type w}
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
      [T2Space A]
      [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]
      [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
      [T2Space C] [@CompleteSpace C (IsTopologicalAddGroup.rightUniformSpace C)]
      [Algebra A C],
      Continuous (algebraMap A C) →
        ∀ φ : MvPolynomial (Fin r) A →ₐ[A] C,
          ∃! ψ : RestrictedPowerSeries (Fin r) A →A[A] C,
            ψ.toAlgHom.comp RestrictedPowerSeries.ofPolynomial = φ)
