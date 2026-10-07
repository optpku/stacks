module

public import stacks_project.Chap68.Lemma_68_8_4_Filtration
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace AlgebraicSpace

/- Lemma 68.8.4: a quasi-compact reasonable algebraic space `X` over `S` admits an
integer `n` and nested open subspaces `∅ = U_{n+1} ⊂ U_n ⊂ ⋯ ⊂ U_1 = X` such that
each reduced difference `T_p = U_p \ U_{p+1}` has a separated-scheme surjective
étale presentation `f_p : V_p ⟶ U_p` that is an isomorphism over `T_p`. -/
@[stacks 07S9] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_finiteSchemeStratumFiltration :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsQuasiCompact X] [IsReasonable X],
      Nonempty (FiniteSchemeStratumFiltration X))

#check AlgebraicGeometry.AlgebraicSpace.FiniteSchemeStratumFiltration
#check AlgebraicGeometry.AlgebraicSpace.FiniteSchemeStratumFiltration.spec

end AlgebraicSpace
end AlgebraicGeometry
