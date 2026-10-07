module

public import stacks_project.Chap68.Lemma_68_8_6_Filtration
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace AlgebraicSpace

/- Lemma 68.8.6: a quasi-compact quasi-separated algebraic space `X` over
`Spec(ℤ)` admits an integer `n` and nested open subspaces
`∅ = U_{n+1} ⊂ U_n ⊂ ⋯ ⊂ U_1 = X` such that each reduced difference
`T_p = U_p \ U_{p+1}` has a quasi-compact separated-scheme surjective étale
presentation `f_p : V_p ⟶ U_p` that is an isomorphism over `T_p`. -/
@[stacks 07ST] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_quasiCompactFiniteSchemeStratumFiltration :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsQuasiCompact X]
      [IsAbsolutelyQuasiSeparated X],
      Nonempty (QuasiCompactFiniteSchemeStratumFiltration X))

#check AlgebraicGeometry.AlgebraicSpace.QuasiCompactFiniteSchemeStratumFiltration
#check AlgebraicGeometry.AlgebraicSpace.QuasiCompactFiniteSchemeStratumFiltration.spec

end AlgebraicSpace
end AlgebraicGeometry
