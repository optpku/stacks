module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Stratification
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace AlgebraicSpace

/- Lemma 68.8.3: a quasi-compact algebraic space `X` over `S` admits nested open
subspaces `… ⊂ U₄ ⊂ U₃ ⊂ U₂ ⊂ U₁ = X` such that each reduced difference
`T_p = U_p \ U_{p+1}` has a separated-scheme surjective étale presentation
`f_p : V_p ⟶ U_p` that is an isomorphism over `T_p`, and every point of `|X|`
represented by a quasi-compact morphism `Spec(k) ⟶ X` from a field lies in
some `T_p`. -/
@[stacks 0BBN] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_schemeStratumFiltration :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsQuasiCompact X],
      Nonempty (SchemeStratumFiltration X))

end AlgebraicSpace
end AlgebraicGeometry
