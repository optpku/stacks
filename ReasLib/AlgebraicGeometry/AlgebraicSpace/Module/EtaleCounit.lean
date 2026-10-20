/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.EpiMono
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- For a quasi-compact separated étale morphism of algebraic spaces and a quasi-coherent
module, the module pullback–pushforward adjunction counit is split epic. -/
@[stacks 0HAP]
instance pullbackPushforwardAdjunction.counit_isSplitEpi
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [Separated f] [Etale f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsSplitEpi ((pullbackPushforwardAdjunction f).counit.app ℱ) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
