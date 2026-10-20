/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.CommAlgCat.Over.Target.Localization
public import ReasLib.RingTheory.Localization.AtPrime.SeparableClosure

@[expose] public section

/-!
# Separable closures of localized target residue maps

This leaf connects the target-kernel localization API with the map-oriented
separable-closure API.  It is independent of strict henselizations and
pointed-etale presentations.

@stack 04GW
-/

universe u v

namespace CommAlgCat.Over.Target.Localization

variable {R : Type u} [CommRing R]
variable {p : Ideal R} [p.IsPrime]
variable {K : Type v} [Field K] [Algebra R K]

/-- With a compatible residue-field scalar tower, the target-localization
residue map agrees with the proof-independent canonical map of `Rₚ`. -/
@[stacks 04GW "target-localization residue map as the canonical prime-local map"]
theorem baseResidueMap_eq_residueMapOfAlgebra
    [Algebra p.ResidueField K] [IsScalarTower R p.ResidueField K]
    (hbase : RingHom.ker (algebraMap R K) = p) :
    baseResidueMap hbase = Localization.AtPrime.residueMapOfAlgebra p := sorry

/-- If `K` is a chosen separable closure of `κ(p)`, then the canonical map
from the residue field of `Rₚ` to `K` is a map-oriented separable closure. -/
@[stacks 04GW "separable closure of a base localized residue map"]
theorem baseResidueMap_isSepClosure
    [Algebra p.ResidueField K] [IsScalarTower R p.ResidueField K]
    [IsSepClosure p.ResidueField K]
    (hbase : RingHom.ker (algebraMap R K) = p) :
    RingHom.IsSepClosure (baseResidueMap hbase) := sorry

end CommAlgCat.Over.Target.Localization
