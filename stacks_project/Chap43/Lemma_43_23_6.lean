/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.Projectivization.ProjectiveLinearGroup
import StacksCheckRecall

open scoped LinearAlgebra.Projectivization

universe u v

/- Lemma 43.23.6: the projective general linear group of a vector space acts doubly
transitively on its projectivization. -/
@[stacks 0B2U] #check
  (Projectivization.projectiveGeneralLinearGroup_is_two_pretransitive :
    ∀ (K : Type u) (V : Type v) [DivisionRing K] [AddCommGroup V] [Module K V],
      MulAction.IsMultiplyPretransitive
        (Projectivization.ProjectiveGeneralLinearGroup K V) (ℙ K V) 2)
