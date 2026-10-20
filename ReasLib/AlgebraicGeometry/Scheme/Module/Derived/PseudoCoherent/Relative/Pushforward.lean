/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.ChangeOfBase
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.ClosedEmbedding
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver

/-- Relative `m`-pseudo-coherence is preserved and reflected by derived pushforward along a
finite morphism. -/
@[stacks 09UK]
theorem iff_pushforward_of_isFinite
    {X Y S : Scheme.{u}} (π : X ⟶ Y) (g : Y ⟶ S) [IsFinite π]
    [LocallyOfFiniteType g] (E : Scheme.DerivedQCoh X) (m : ℤ) :
    IsMPseudoCoherentOver (π ≫ g) E.obj m ↔
      IsMPseudoCoherentOver g
        ((Scheme.DerivedQCoh.pushforwardCohomologyIn π).obj E).obj m := sorry

/-- Relative `m`-pseudo-coherence is preserved and reflected by derived pushforward along a
locally finite type morphism whose underlying map is a closed embedding. -/
@[stacks 09VG]
theorem iff_pushforward_of_isClosedEmbedding
    {X Y S : Scheme.{u}} (i : X ⟶ Y) (g : Y ⟶ S)
    [LocallyOfFiniteType i] [LocallyOfFiniteType g]
    (hi : Topology.IsClosedEmbedding i.base) (E : DerivedCategory X.Modules) (m : ℤ) :
    IsMPseudoCoherentOver (i ≫ g) E m ↔
      IsMPseudoCoherentOver g
        ((RingedSpace.moduleDerivedPushforward i.toShHom).obj E) m := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver
