/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent.Relative.Module
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry

universe u

/- Definition 76.45.3 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is locally of finite type. Let `E` be an object
of `D_QCoh(𝒪_X)`. Fix `m : ℤ`. We say `E` is `m`-pseudo-coherent relative to `Y`
if the equivalent conditions of Lemma 76.45.2 are satisfied. -/
@[stacks 0CSY] #check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsMPseudoCoherentOver :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f], ModuleDerived X → ℤ → Prop)

/- Definition 76.45.3 (2): We say `E` is pseudo-coherent relative to `Y` if `E`
is `m`-pseudo-coherent relative to `Y` for all `m : ℤ`. -/
@[stacks 0CSY] #check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPseudoCoherentOver :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f], ModuleDerived X → Prop)

/- Definition 76.45.3 (3): Let `F` be a quasi-coherent `𝒪_X`-module. We say `F`
is `m`-pseudo-coherent relative to `Y` if `F` viewed as an object of
`D_QCoh(𝒪_X)` is `m`-pseudo-coherent relative to `Y`. -/
@[stacks 0CSY] #check (AlgebraicGeometry.AlgebraicSpace.Modules.IsMPseudoCoherentOver :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules) (f : X ⟶ Y)
    [LocallyOfFiniteType f], ℤ → Prop)

/- Definition 76.45.3 (4): We say `F` is pseudo-coherent relative to `Y` if `F`
viewed as an object of `D_QCoh(𝒪_X)` is pseudo-coherent relative to `Y`. -/
@[stacks 0CSY] #check (AlgebraicGeometry.AlgebraicSpace.Modules.IsPseudoCoherentOver :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules) (f : X ⟶ Y)
    [LocallyOfFiniteType f], Prop)
