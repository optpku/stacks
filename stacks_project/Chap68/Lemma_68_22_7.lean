/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap68.Lemma_68_22_7_Map
public import stacks_project.Chap68.Lemma_68_22_7_Normalization
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 68.22.7 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a birational
morphism between algebraic spaces over `S` which are decent and have finitely
many irreducible components. Then the normalizations `X.normalization ⟶ X` and
`Y.normalization ⟶ Y` exist. -/
@[stacks 0BBG] #check
  (HasFiniteIrreducibleComponentsOnCompactOpens.of_isDecent :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsDecent X] [HasFiniteIrreducibleComponents X],
      HasFiniteIrreducibleComponentsOnCompactOpens X)

/- Lemma 68.22.7 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a birational
morphism between algebraic spaces over `S` which are decent and have finitely
many irreducible components. Then there is a commutative diagram of algebraic
spaces over `S` with vertical arrows `X.normalizationTo` and
`Y.normalizationTo`, and the morphism `X.normalization ⟶ Y.normalization` is
birational. -/
@[stacks 0BBG] #check
  (IsBirational.exists_normalizationMap :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
      [IsDecent X] [IsDecent Y]
      [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
      (f : X ⟶ Y) [IsBirational f],
      ∃ g : X.normalization ⟶ Y.normalization,
        g ≫ Y.normalizationTo = X.normalizationTo ≫ f ∧ IsBirational g)
