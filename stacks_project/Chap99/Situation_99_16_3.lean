/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.Category
public import stacks_project.Chap99.Situation_99_16_3_Category

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Situation 99.16.3: for a proper, flat, finite-presentation morphism
`f : X ⟶ B` of algebraic spaces over a scheme `S`, `Complexes.category f` is the category
of triples `(T, g, E)` where `T` is a scheme over `S`, `g : T ⟶ B` is a morphism
over `S`, and setting `X_T = T ×_B X`, the object `E` of `D(𝒪_{X_T})` is
`T`-perfect and has vanishing negative self-Ext groups on field-valued fibres
over `T`. A morphism `(T, g, E) ⟶ (T', g', E')` is a pair `(h, φ)` where
`h : T ⟶ T'` is a morphism of schemes over `B` and
`φ : L(h')^* E' ≅ E` is an isomorphism in `D(𝒪_{X_T})`, where
`h' : X_T ⟶ X_{T'}` is the base change of `h`. -/
@[stacks 0DLE] #check (AlgebraicGeometry.AlgebraicSpace.Complexes.category :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f], CategoryTheory.Cat.{u + 1, u + 1})
