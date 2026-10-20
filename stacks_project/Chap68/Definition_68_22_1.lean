/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Birational
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 68.22.1: Let `S` be a scheme. Let `X` and `Y` be algebraic spaces over `S`.
Assume `X` and `Y` are decent and that `|X|` and `|Y|` have finitely many irreducible
components. A morphism `f : X ⟶ Y` is birational if `|f|` induces a bijection between
the generic points of irreducible components of `|X|` and those of `|Y|`, and for every
generic point `x` of an irreducible component of `|X|` the local ring map
`𝒪_{Y, f(x)} ⟶ 𝒪_{X, x}` is an isomorphism. -/
@[stacks 0ACV] #check (AlgebraicGeometry.AlgebraicSpace.IsBirational :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y],
    (X ⟶ Y) → Prop)
#check (AlgebraicGeometry.AlgebraicSpace.isBirational_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y),
    IsBirational f ↔
      Set.BijOn (Points.map f) (genericPoints X) (genericPoints Y) ∧
        ∀ {x : Points X}, x ∈ genericPoints X → IsIsoStalkMapAt f x)
