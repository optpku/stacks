module

public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap71.Lemma_71_19_3_AdmissibleBlowup

/-!
# Separating open subspaces by admissible blowups

Two disjoint quasi-compact open subspaces of a quasi-compact quasi-separated
algebraic space can be separated by an admissible blowup of their union.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Two disjoint quasi-compact open subspaces of a quasi-compact quasi-separated
algebraic space have disjoint inverse images contained in a two-open cover after
an admissible blowup of their union. -/
theorem exists_isAdmissibleBlowup_disjointOpenCover_of_disjoint_qc_opens
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (U V : OpenSubspace X) [QuasiCompact U.ι] [QuasiCompact V.ι]
    (hUV : Disjoint U.pointsSet V.pointsSet) :
    ∃ (X' : AlgebraicSpace S) (b : X' ⟶ X) (X₁ X₂ : OpenSubspace X'),
      IsAdmissibleBlowup (OpenSubspace.ofOpens (U.pointsOpens ⊔ V.pointsOpens)) b ∧
        Disjoint X₁.pointsSet X₂.pointsSet ∧
          X₁.pointsOpens ⊔ X₂.pointsOpens = ⊤ ∧
            Points.map b ⁻¹' U.pointsSet ⊆ X₁.pointsSet ∧
              Points.map b ⁻¹' V.pointsSet ⊆ X₂.pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
