/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberStalkDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ResidueFieldTrdeg
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 67.33.1 (1): let `S` be a scheme, let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`, let `x` be a point of `|X|`, and let `d : ℕ∞`. The
dimension of the local ring of the fibre of `f` at `x` is `d` if the equivalent
conditions of Lemma 67.22.5 hold for `fiberStalkKrullDimEq d`. -/
@[stacks 04NM] #check (AlgebraicGeometry.AlgebraicSpace.FiberStalkDimEqAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
    (X ⟶ Y) → ℕ∞ → AlgebraicSpace.Points X → Prop)

/- Definition 67.33.1 (2): let `S` be a scheme, let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`, let `x` be a point of `|X|`, and let `r : ℕ∞`. The
transcendence degree of `x / f(x)` is `r` if the equivalent conditions of
Lemma 67.22.5 hold for `residueFieldTrdegEq r`. -/
@[stacks 04NM] #check (AlgebraicGeometry.AlgebraicSpace.ResidueFieldTrdegEqAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
    (X ⟶ Y) → ℕ∞ → AlgebraicSpace.Points X → Prop)

/- Definition 67.33.1 (3): let `S` be a scheme, let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`, let `x` be a point of `|X|`, and let `d : ℕ∞`. The
morphism `f` has relative dimension `d` at `x` if the equivalent conditions of
Lemma 67.22.5 hold for the property that `dim_u(U_v)` equals `d`. -/
@[stacks 04NM] #check (AlgebraicGeometry.AlgebraicSpace.RelativeDimensionEqAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
    (X ⟶ Y) → ℕ∞ → AlgebraicSpace.Points X → Prop)
