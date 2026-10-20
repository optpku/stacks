/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap71.Lemma_71_4_6_RelativeAssassin
import StacksCheckRecall

/-!
# Definition 71.4.5

The relative weak assassin `relativeWeakAss f F ⊂ |X|` of a quasi-coherent
`𝒪_X`-module along a morphism of algebraic spaces, and the notation
`relativeAssassin f F` when the fibres are locally Noetherian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Definition 71.4.5 (1): let `S` be a scheme, let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`, and let `F` be a quasi-coherent `𝒪_X`-module. The
relative weak assassin of `F` in `X` over `Y` is the set
`relativeWeakAss f F ⊂ |X|` of those `x` in `|X|` such that the equivalent
conditions of Lemma 71.4.4 hold. -/
@[stacks 0CV0] #check
  (@Modules.relativeWeakAss :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (X ⟶ Y) → X.Modules → Set (Points X))

/- Definition 71.4.5 (2): if the fibres of `f` are locally Noetherian
(`LocallyNoetherianFibers f`, Definition 71.4.2), the same set is written
`relativeAssassin f F`. -/
@[stacks 0CV0] #check
  (@Modules.relativeAssassin :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (X ⟶ Y) → X.Modules → Set (Points X))

#check Modules.mem_relativeWeakAss_iff
#check Modules.mem_relativeAssassin_iff
