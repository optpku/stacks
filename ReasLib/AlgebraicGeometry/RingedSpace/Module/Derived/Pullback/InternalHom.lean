/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Bounded.Local
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatMorphism
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TorDimension.Morphism
public import ReasLib.CategoryTheory.Monoidal.Closed.LaxMonoidal.Dualizable
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived pullback and internal Hom

The comparison morphism is the canonical one attached to the strong monoidal derived pullback
functor.  Perfectness, flat pseudo-coherence, and finite Tor dimension give three independent
criteria for its invertibility.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.modulePullbackDerived.InternalHom

variable {X Y : RingedSpace.{u}}
variable [MonoidalCategory (ModuleDerived X)] [MonoidalClosed (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived Y)] [MonoidalClosed (ModuleDerived Y)]
variable (f : X ⟶ Y) [(modulePullbackDerived f).Monoidal]

/-- The canonical comparison from derived pullback of an internal Hom to the internal Hom of the
derived pullbacks. -/
@[stacks 0GM7 "canonical comparison"]
noncomputable abbrev comparison (K M : ModuleDerived Y) :
    (modulePullbackDerived f).obj ((ihom K).obj M) ⟶
      (ihom ((modulePullbackDerived f).obj K)).obj
        ((modulePullbackDerived f).obj M) :=
  Functor.LaxMonoidal.InternalHom.comparison (modulePullbackDerived f) K M

/-- Lemma 20.51.3 (1): derived pullback preserves internal Hom out of a perfect object. -/
@[stacks 0GM7 "(1)"]
theorem isIso_of_isPerfect {K M : ModuleDerived Y}
    (hK : ModuleDerived.IsPerfect K) :
    IsIso (comparison f K M) := sorry

/-- Lemma 20.51.3 (2): along a flat morphism, derived pullback preserves internal Hom from a
pseudo-coherent object into a locally bounded-below object. -/
@[stacks 0GM7 "(2)"]
theorem isIso_of_isFlat [RingedSpace.Hom.IsFlat f]
    {K M : ModuleDerived Y} (hK : ModuleDerived.IsPseudoCoherent K)
    (hM : ModuleDerived.IsLocallyBoundedBelow M) :
    IsIso (comparison f K M) := sorry

/-- Lemma 20.51.3 (3): a finite-Tor-dimension morphism preserves internal Hom from a
pseudo-coherent object into a locally bounded-below object. -/
@[stacks 0GM7 "(3)"]
theorem isIso_of_finiteTorDimension [RingedSpace.Hom.HasFiniteTorDimension f]
    {K M : ModuleDerived Y} (hK : ModuleDerived.IsPseudoCoherent K)
    (hM : ModuleDerived.IsLocallyBoundedBelow M) :
    IsIso (comparison f K M) := sorry

end AlgebraicGeometry.RingedSpace.modulePullbackDerived.InternalHom
