/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Specialization
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 68.12.2: Let `S` be a scheme. Let `X` be a decent algebraic space over
`S`. Let `x, x' : Points X` and assume `x' ⤳ x`, i.e., `x` is a specialization of
`x'`. Then for every étale morphism `φ : ofOver U ⟶ X` from a scheme `U` and any
`u : U.left` with `Points.mapOfOver φ u = x`, there exists a point `u' : U.left`
with `u' ⤳ u` and `Points.mapOfOver φ u' = x'`. -/
@[stacks 03IL] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_specializes_of_isDecent :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsDecent X] {x x' : Points X} (hspec : Specializes x' x) {U : Over S}
      (φ : ofOver U ⟶ X) [Etale φ] {u : U.left}
      (hu : Points.mapOfOver φ u = x),
      ∃ u' : U.left, Specializes u' u ∧ Points.mapOfOver φ u' = x')

#check
  (AlgebraicGeometry.AlgebraicSpace.generalizingMap_mapOfOver :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsDecent X] {U : Over S} (φ : ofOver U ⟶ X) [Etale φ],
      GeneralizingMap (Points.mapOfOver φ))
