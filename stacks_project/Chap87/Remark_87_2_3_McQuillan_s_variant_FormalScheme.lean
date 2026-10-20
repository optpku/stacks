/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalScheme.McQuillan
public import stacks_project.Chap87.«87_2_0_2_FormalScheme»
public import stacks_project.Chap87.Remark_87_2_3_McQuillan_s_variant_Spf

@[expose] public section

universe u

noncomputable section

namespace AlgebraicGeometry.McQuillan.FormalScheme

/-- The weak formal spectrum with its record presentation of the open prime space. -/
def ofSpf (A : TopCommRingCat.{u}) (hA : TopologicalRing.IsWeaklyAdmissibleRing A) :
    AlgebraicGeometry.McQuillan.FormalScheme.{u} :=
  ofSpfOnSpace A hA legacyOpenPrimeHomeomorph

/-- The underlying locally topologically ringed space is the transported weak formal spectrum. -/
theorem ofSpf_toLocallyTopologicallyRingedSpace (A : TopCommRingCat.{u})
    (hA : TopologicalRing.IsWeaklyAdmissibleRing A) :
    (ofSpf A hA).toLocallyTopologicallyRingedSpace =
      spfOnSpace A hA legacyOpenPrimeHomeomorph := rfl

end AlgebraicGeometry.McQuillan.FormalScheme
