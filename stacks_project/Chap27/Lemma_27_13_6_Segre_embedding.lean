/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ProjectiveSpace.Segre

open CategoryTheory
open CategoryTheory.Limits

universe u

/- Lemma 27.13.6 (Segre embedding): for every scheme `S` and chosen relative projective spaces
of dimensions `n` and `m`, their fibre product over `S` admits a closed immersion over `S` into
a relative projective space of dimension `n * m + n + m`. -/
@[stacks 01WD] #check
  (AlgebraicGeometry.ProjectiveSpaceOver.exists_segreEmbedding :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {n m : ℕ}
      (P : AlgebraicGeometry.ProjectiveSpaceOver S n)
      (Q : AlgebraicGeometry.ProjectiveSpaceOver S m),
      ∃ (R : AlgebraicGeometry.ProjectiveSpaceOver S (n * m + n + m))
        (i : pullback P.hom Q.hom ⟶ R.scheme),
        AlgebraicGeometry.IsClosedImmersion i ∧
          i ≫ R.hom = pullback.fst P.hom Q.hom ≫ P.hom)
