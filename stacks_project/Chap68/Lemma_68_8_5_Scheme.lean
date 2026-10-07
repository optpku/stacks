module

public import stacks_project.Chap68.Lemma_68_8_4_Filtration
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme

/-!
# Scheme strata of a finite nested open filtration

This file records that each reduced difference of a finite scheme-stratum
filtration is a scheme, and the corresponding existence statement for a
quasi-compact reasonable algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

namespace FiniteSchemeStratumFiltration

/-- Each reduced difference of a finite scheme-stratum filtration is a scheme. -/
theorem isScheme_reducedStratum (F : FiniteSchemeStratumFiltration X) (n : ℕ) :
    IsScheme (reducedStratum F.openStage n).X :=
  sorry

end FiniteSchemeStratumFiltration

/-- A quasi-compact reasonable algebraic space admits a finite nested open
filtration whose successive reduced differences are schemes. -/
theorem exists_openFiltration_reducedStratum_isScheme (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsReasonable X] :
    ∃ (n : ℕ) (U : ℕ → OpenSubspace X),
      Antitone (fun i ↦ (U i).pointsSet) ∧
        (U 0).pointsSet = Set.univ ∧
        (U n).pointsSet = ∅ ∧
        ∀ i, IsScheme (reducedStratum U i).X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
