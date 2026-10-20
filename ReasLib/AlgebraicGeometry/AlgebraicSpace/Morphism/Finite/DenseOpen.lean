/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Extending finiteness from a dense open

A flat proper morphism of algebraic spaces is finite if it is finite after
base change to a topologically dense open subspace, and either the morphism
is locally of finite presentation or the open inclusion is quasi-compact.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsFinite

/-- A flat proper morphism of algebraic spaces is finite if it
is finite after base change to a topologically dense open subspace, and either
the morphism is locally of finite presentation or the open inclusion is
quasi-compact. -/
@[stacks 0B4J]
theorem of_restrict_of_flat {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [Proper f] (V : OpenSubspace Y)
    (hV_dense : Dense V.pointsSet) [IsFinite (pullback.snd f V.ι)]
    (h_finitePresentation_or_quasiCompact :
      LocallyOfFinitePresentation f ∨ QuasiCompact V.ι) :
    IsFinite f :=
  sorry

/-- A flat proper morphism of algebraic spaces locally of finite presentation
is finite if it is finite after base change to a topologically dense open
subspace. -/
theorem of_restrict_of_flat_of_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Flat f] [Proper f]
    [LocallyOfFinitePresentation f] (V : OpenSubspace Y)
    (hV_dense : Dense V.pointsSet) [IsFinite (pullback.snd f V.ι)] :
    IsFinite f :=
  of_restrict_of_flat f V hV_dense (Or.inl inferInstance)

/-- A flat proper morphism of algebraic spaces is finite if it is finite after
base change to a quasi-compact topologically dense open subspace. -/
theorem of_restrict_of_flat_of_quasiCompact {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Flat f] [Proper f]
    (V : OpenSubspace Y) (hV_dense : Dense V.pointsSet)
    [IsFinite (pullback.snd f V.ι)] [QuasiCompact V.ι] :
    IsFinite f :=
  of_restrict_of_flat f V hV_dense (Or.inr inferInstance)

end AlgebraicGeometry.AlgebraicSpace.IsFinite
