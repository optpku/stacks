/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.Diagonal

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Correspondence
open AlgebraicGeometry.Scheme.Modules
open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 45.6.2 -/
@[stacks 0FGR]
#check (AlgebraicGeometry.ChowGroup.ProjectiveBundle.diagonal_formula :
  {k : Type u} → [Field k] →
    (X P : Correspondence.Category k) →
      (E : Scheme.Modules X.scheme.left) →
        (p : P.scheme ⟶ X.scheme) →
          (hp : Scheme.ProjectiveBundle.Representation p.left E) →
            (q : ℕ) →
              [IsFiniteLocallyFreeOfRank (q + 1) E] →
                Correspondence.integralGraph (𝟙 P.scheme) =
                  Correspondence.castHom (Category.id_comp prod.snd) 0
                    (BivariantClass.Nonnegative.castGrading (fun _ ↦ 0)
                      (add_neg_cancel (q : ℤ))
                      (BivariantClass.comp (fun _ ↦ 0) (𝟙 (P.scheme ⨯ P.scheme))
                        prod.snd
                        (AlgebraicGeometry.ChowGroup.ProjectiveBundle.diagonalChernClass
                          X P E p hp q)
                        (AlgebraicGeometry.ChowGroup.ProjectiveBundle.baseDiagonalClass
                          X P E p hp q))))
