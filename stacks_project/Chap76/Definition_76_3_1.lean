/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Radicial
import StacksCheckRecall

open CategoryTheory

universe u

/- Definition 76.3.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. We say `f` is radicial if for any morphism
`Spec(K) ⟶ Y` where `K` is a field the reduction `(Spec(K) ×_Y X)_red` is either
empty or representable by the spectrum of a purely inseparable field extension of
`K`. -/
@[stacks 0481]
#check (AlgebraicGeometry.AlgebraicSpace.Radicial :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → Prop)
