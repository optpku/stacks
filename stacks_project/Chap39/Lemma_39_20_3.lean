/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Representability
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/- Lemma 39.20.3: if `q : U ⟶ M` equalizes `P.t` and `P.s`, and both `q` and
`(P.t, P.s) : P.left ⟶ U ×_M U` induce locally surjective maps of sheaves for `τ`,
then the canonical comparison from `U/R` to the sheaf represented by `M` is an isomorphism. -/
@[stacks 03C5] #check
  (AlgebraicGeometry.Scheme.PreRelation.quotientSheafDesc_isIso_of_locallySurjective :
    ∀ {S : Scheme.{u}} (τ : StandardTopology) {U M : Over S}
      (P : PreRelation U) (q : U ⟶ M)
      (h_equalizes : P.t ≫ q = P.s ≫ q),
      Sheaf.IsLocallySurjective
        ((τ.overTopology S).uliftYoneda.{u + 1}.map q)
      → Sheaf.IsLocallySurjective
        ((τ.overTopology S).uliftYoneda.{u + 1}.map
          (P.kernelPairLift q h_equalizes))
      → IsIso (P.quotientSheafDesc (τ.overTopology S) q h_equalizes))

end AlgebraicGeometry.Scheme.PreRelation
