module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Separation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 71.19.5: let `S` be a scheme. Let `X` be a quasi-compact and quasi-separated
algebraic space over `S`. Let `U, V` be quasi-compact disjoint open subspaces of `X`.
Then there exists a `(U ∪ V)`-admissible blowup `b : X' ⟶ X` such that `X'` is a
disjoint union of open subspaces `X' = X₁ ∐ X₂` with `Points.map b ⁻¹' U.pointsSet ⊆
X₁.pointsSet` and `Points.map b ⁻¹' V.pointsSet ⊆ X₂.pointsSet`. -/
@[stacks 086F] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_isAdmissibleBlowup_disjointOpenCover_of_disjoint_qc_opens :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
      [IsAbsolutelyQuasiSeparated X] (U V : OpenSubspace X)
      [QuasiCompact U.ι] [QuasiCompact V.ι],
      Disjoint U.pointsSet V.pointsSet →
        ∃ (X' : AlgebraicSpace S) (b : X' ⟶ X) (X₁ X₂ : OpenSubspace X'),
          IsAdmissibleBlowup (OpenSubspace.fromOpens (U.pointsOpens ⊔ V.pointsOpens)) b ∧
            Disjoint X₁.pointsSet X₂.pointsSet ∧
              X₁.pointsOpens ⊔ X₂.pointsOpens = ⊤ ∧
                Points.map b ⁻¹' U.pointsSet ⊆ X₁.pointsSet ∧
                  Points.map b ⁻¹' V.pointsSet ⊆ X₂.pointsSet)
