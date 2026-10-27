/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalScheme.IdealSystem

/-!
# Fundamental systems of ideals of definition

The canonical affine-section criterion and the family of each bundled system.
-/

@[expose] public section

universe u

open CategoryTheory Opposite Topology AlgebraicGeometry

namespace AlgebraicGeometry.FormalScheme

#check (AlgebraicGeometry.FormalScheme.isFundamentalSystem_iff :
  ∀ {X : FormalScheme.{u}} {ι : Type u}
    (I : ι → IdealSheafData X),
    IsFundamentalSystem I ↔
      ∀ U : X.affineOpens,
        TopologicalRing.Ideal.IsFundamentalSystemOfIdeals (fun i ↦ (I i).ideal U))

#check (AlgebraicGeometry.FormalScheme.FundamentalSystem.isFundamental :
  ∀ {X : FormalScheme.{u}} (S : FundamentalSystem X),
    IsFundamentalSystem S.ideal)

end AlgebraicGeometry.FormalScheme
