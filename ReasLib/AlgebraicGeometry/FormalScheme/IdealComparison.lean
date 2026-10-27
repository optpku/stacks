/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalScheme.IdealSystem
public import ReasLib.AlgebraicGeometry.FormalScheme.McQuillan.WeakIdealSystem

/-!
# Ideals under the EGA–McQuillan comparison
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Opposite TopologicalSpace Topology AlgebraicGeometry TopologicalRing

namespace AlgebraicGeometry.FormalScheme

/-- An EGA formal affine open remains a McQuillan formal affine open on the
image of `ofFormalScheme`. -/
theorem isAffineOpen_ofFormalScheme {X : FormalScheme.{u}} {U : Opens X.carrier}
    (hU : IsAffineOpen U) :
    McQuillan.FormalScheme.IsAffineOpen
      (X := McQuillan.FormalScheme.ofFormalScheme.obj X) U :=
  sorry

/-- Restrict a McQuillan ideal sheaf on `ofFormalScheme.obj X` to EGA affine
opens of `X`. -/
def IdealSheafData.ofMcQuillan {X : FormalScheme.{u}}
    (I : McQuillan.FormalScheme.IdealSheafData
      (McQuillan.FormalScheme.ofFormalScheme.obj X)) :
    IdealSheafData X where
  ideal U :=
    I.ideal
      ⟨(U.1 : Opens (McQuillan.FormalScheme.ofFormalScheme.obj X).carrier),
        isAffineOpen_ofFormalScheme U.2⟩
  map_ideal {U V} h :=
    I.map_ideal
      (U := ⟨U.1, isAffineOpen_ofFormalScheme U.2⟩)
      (V := ⟨V.1, isAffineOpen_ofFormalScheme V.2⟩) h
  local_mem := sorry

/-- On an EGA formal affine open, `ofMcQuillan` recovers the McQuillan
component. -/
theorem IdealSheafData.ofMcQuillan_ideal {X : FormalScheme.{u}}
    (I : McQuillan.FormalScheme.IdealSheafData
      (McQuillan.FormalScheme.ofFormalScheme.obj X))
    (U : X.affineOpens) :
    (IdealSheafData.ofMcQuillan I).ideal U =
      I.ideal
        ⟨(U.1 : Opens (McQuillan.FormalScheme.ofFormalScheme.obj X).carrier),
          isAffineOpen_ofFormalScheme U.2⟩ :=
  rfl

/-- A nonempty directed decreasing weak fundamental system on a quasi-compact formal scheme
consists eventually of ideals of definition. -/
theorem eventually_isIdealOfDefinition {X : FormalScheme.{u}}
    [CompactSpace X.carrier]
    (S : McQuillan.FormalScheme.FundamentalSystem (McQuillan.FormalScheme.ofFormalScheme.obj X))
    (hne : Nonempty S.ι)
    [Preorder S.ι] [IsDirected S.ι (· ≤ ·)]
    (hnest : ∀ i j, i ≤ j → ∀ U : (McQuillan.FormalScheme.ofFormalScheme.obj X).affineOpens,
      (S.ideal j).ideal U ≤ (S.ideal i).ideal U) :
    ∃ i, ∀ j, i ≤ j →
      IsIdealOfDefinition (IdealSheafData.ofMcQuillan (S.ideal j)) :=
  sorry

/-- On a quasi-compact EGA formal scheme, a fundamental system of ideals of
definition exists if and only if the McQuillan embedding admits a fundamental
system of weak ideals of definition. -/
theorem exists_fundamentalSystem_iff_exists_weakFundamentalSystem
    {X : FormalScheme.{u}} [CompactSpace X.carrier] :
    Nonempty (FundamentalSystem X) ↔
      Nonempty
        (McQuillan.FormalScheme.FundamentalSystem
          (McQuillan.FormalScheme.ofFormalScheme.obj X)) :=
  sorry

end AlgebraicGeometry.FormalScheme
