/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Lemma_71_19_4_CommonRefinement
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 71.19.4: let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated algebraic space over `S`. Let `U ⊂ X` be a quasi-compact open
subspace. Let `bᵢ : Xᵢ ⟶ X` be a finite family of `U`-admissible blowups.
There exists a `U`-admissible blowup `b : X' ⟶ X` which factors through every
`bᵢ`, and each comparison `X' ⟶ Xᵢ` is a `U`-admissible blowup. -/
@[stacks 086E] #check
  (exists_isAdmissibleBlowup_common_refinement :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
      [IsAbsolutelyQuasiSeparated X] (U : OpenSubspace X)
      [QuasiCompact U.ι] {n : ℕ} (Xi : Fin n → AlgebraicSpace S)
      (bi : ∀ i : Fin n, Xi i ⟶ X),
      (∀ i : Fin n, IsAdmissibleBlowup U (bi i)) →
      ∃ (X' : AlgebraicSpace S) (b : X' ⟶ X),
        IsAdmissibleBlowup U b ∧
          ∀ i : Fin n, ∃ c : X' ⟶ Xi i,
            c ≫ bi i = b ∧
              IsAdmissibleBlowup (U.inverseImage (bi i)) c)
