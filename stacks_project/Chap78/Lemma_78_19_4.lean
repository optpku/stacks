/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientSheaf.Representability

/-!
# Lemma 78.19.4

If an algebraic space `M` over `S` and a morphism `q : U ⟶ M` equalize `s` and `t`,
and both `q` and `(t, s) : R ⟶ U ×_M U` are surjections of fppf sheaves, then `M`
represents the quotient sheaf `U/R`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/- Lemma 78.19.4: in the situation of Definition 78.19.1, if an algebraic space `M` over `S`
and a morphism `q : U.left ⟶ M` equalize `s` and `t`, `q` is a surjection of fppf sheaves, and
the induced map `(t, s) : R ⟶ U ×_M U` is a surjection of fppf sheaves, then the canonical
comparison `U/R ⟶ toSheaf.obj M` is an isomorphism of fppf sheaves. -/
@[stacks 044M]
#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.quotientSheafDesc_isIso_of_locallySurjective :
  ∀ {S : Scheme.{u}}
    {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) {M : AlgebraicSpace S}
    (q : U.left ⟶ M) (h_equalizes : P.t.left ≫ q = P.s.left ≫ q)
    (h_q : Sheaf.IsLocallySurjective (toSheaf.map q))
    (h_kernel : Sheaf.IsLocallySurjective
      (toSheaf.map (P.kernelPairLift q h_equalizes))),
    IsIso (P.quotientSheafDesc q h_equalizes))

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.quotientSheafDesc_isIso :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {M : AlgebraicSpace S} (q : U.left ⟶ M)
    (h_equalizes : P.t.left ≫ q = P.s.left ≫ q)
    [h_q : Sheaf.IsLocallySurjective (toSheaf.map q)]
    [h_kernel : Sheaf.IsLocallySurjective
      (toSheaf.map (P.kernelPairLift q h_equalizes))],
    IsIso (P.quotientSheafDesc q h_equalizes))

end AlgebraicGeometry.AlgebraicSpace.PreRelation
