/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Birational
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Decent
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 68.22.7: Let `S` be a scheme. Let `f : X ⟶ Y` be a birational
morphism between algebraic spaces over `S` which are decent and have finitely
many irreducible components. Then the normalizations `X.normalization ⟶ X` and
`Y.normalization ⟶ Y` exist, and there is a commutative diagram of algebraic
spaces over `S` with vertical arrows `X.normalizationTo` and
`Y.normalizationTo`. The induced morphism `X.normalization ⟶ Y.normalization`
is birational. The normalization-existence premise of finitely many irreducible
components on compact opens follows from decency and finite irreducible
components, as checked below. -/
@[stacks 0BBG] #check
  (AlgebraicGeometry.AlgebraicSpace.IsBirational.exists_normalizationMap :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
      [IsDecent X] [IsDecent Y]
      [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
      (f : X ⟶ Y) [IsBirational f],
      ∃ g : X.normalization ⟶ Y.normalization,
        g ≫ Y.normalizationTo = X.normalizationTo ≫ f ∧ IsBirational g)

#check
  (AlgebraicGeometry.AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens.of_isDecent :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsDecent X] [HasFiniteIrreducibleComponents X],
      HasFiniteIrreducibleComponentsOnCompactOpens X)
