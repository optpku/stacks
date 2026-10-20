module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Stratification.Finite
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace AlgebraicSpace

/- Lemma 68.8.5: a quasi-compact reasonable algebraic space `X` over `S` admits an
integer `n` and nested open subspaces `∅ = U_{n+1} ⊂ U_n ⊂ ⋯ ⊂ U_1 = X` such that
each reduced difference `T_p = U_p \ U_{p+1}` is a scheme. -/
@[stacks 07SA] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_openFiltration_reducedStratum_isScheme :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsQuasiCompact X] [IsReasonable X],
      ∃ (n : ℕ) (U : ℕ → OpenSubspace X),
        Antitone (fun i ↦ (U i).pointsSet) ∧
          (U 0).pointsSet = Set.univ ∧
          (U n).pointsSet = ∅ ∧
          ∀ i, IsScheme (reducedStratum U i).X)

#check AlgebraicGeometry.AlgebraicSpace.FiniteSchemeStratumFiltration.isScheme_reducedStratum

end AlgebraicSpace
end AlgebraicGeometry
