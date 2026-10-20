/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cohomology of pseudo-coherent derived modules on ringed spaces

This leaf specializes the ringed-site finiteness API and uses the canonical ringed-space
`cohomologySheaf` owner in its public statements.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent

variable {X : RingedSpace.{u}} {K : ModuleDerived X} {m : ℤ}

/-- Lemma 20.47.9 (1): the top cohomology sheaf of an `m`-pseudo-coherent object in
`D^{≤ m}` is of finite type. -/
@[stacks 08DN "(1)"]
theorem topCohomology_isFiniteType
    (hK : IsMPseudoCoherent K m) (hLE : K.IsLE m) :
    (cohomologySheaf K m).IsFiniteType := sorry

/-- Lemma 20.47.9 (2): degree `m + 1` cohomology of an `m`-pseudo-coherent object in
`D^{≤ m + 1}` is finitely presented. -/
@[stacks 08DN "(2)"]
theorem nextCohomology_isFinitePresentation
    (hK : IsMPseudoCoherent K m) (hLE : K.IsLE (m + 1)) :
    (cohomologySheaf K (m + 1)).IsFinitePresentation := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent
