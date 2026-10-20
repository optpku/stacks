/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.Fiber
public import Mathlib.Topology.Connected.TotallyDisconnected

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/-- An equivalence on finite étale schemes induces a homeomorphism on connected
components of quasi-compact, quasi-separated schemes. -/
theorem AlgebraicGeometry.Scheme.connectedComponentsHomeomorph_of_finiteEtaleBaseChange
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] (f : X ⟶ Y)
    [Functor.IsEquivalence (Scheme.finiteEtaleBaseChange f)] :
    IsHomeomorph f.continuous.connectedComponentsMap := sorry

/-- A finite étale base-change equivalence between quasi-compact,
quasi-separated schemes with connected source induces a homeomorphism of
étale fundamental groups at a geometric point and its image. -/
theorem AlgebraicGeometry.Scheme.fundamentalGroupIso_of_finiteEtaleBaseChange
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] (f : X ⟶ Y)
    [Functor.IsEquivalence (Scheme.finiteEtaleBaseChange f)] [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    IsHomeomorph (AlgebraicGeometry.Scheme.Hom.fundamentalGroupMap f s) := sorry
