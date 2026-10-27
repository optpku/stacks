/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Relative.Locus
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
  (AlgebraicGeometry.AlgebraicSpace.Modules.relativeWeakAss :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (X ⟶ Y) → X.Modules → Set (Points X))

/- Definition 71.4.5 (2): if the fibres of `f` are locally Noetherian
(`LocallyNoetherianFibers f`, Definition 71.4.2), the same set is written
`relativeAssassin f F`. -/
@[stacks 0CV0] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.relativeAssassin :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (X ⟶ Y) → X.Modules → Set (Points X))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mem_relativeWeakAss_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (F : X.Modules) (x : Points X),
    x ∈ Modules.relativeWeakAss f F ↔
      ∃ (p : FieldValuedPoint Y) (t : Points (fieldFiber f p)),
        Points.mk p = Points.map f x ∧
          Points.map (fieldFiberι f p) t = x ∧
            t ∈ ((Modules.pullback (fieldFiberι f p)).obj F).weakAss)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mem_relativeAssassin_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (F : X.Modules) (x : Points X),
    x ∈ Modules.relativeAssassin f F ↔
      ∃ (p : FieldValuedPoint Y) (t : Points (fieldFiber f p)),
        Points.mk p = Points.map f x ∧
          Points.map (fieldFiberι f p) t = x ∧
            t ∈ ((Modules.pullback (fieldFiberι f p)).obj F).weakAss)
