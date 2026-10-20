/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedPoints

/-!
# Weakly associated points of module sheaves on algebraic spaces

The weakly associated locus is defined by weak association at geometric stalks.
For quasi-coherent modules it can also be tested on an étale scheme chart.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The set of weakly associated points of an `𝒪_X`-module. -/
def weakAss (F : X.Modules) : Set (Points X) :=
  etaleStalkWeakAss F

/-- Membership in the weakly associated locus is the étale-stalk weak-association
predicate. -/
theorem mem_weakAss_iff (F : X.Modules) (x : Points X) :
    x ∈ F.weakAss ↔ etaleStalkWeakAss F x :=
  Iff.rfl

/-- For a quasi-coherent module, membership in the weakly associated locus is equivalent to weak
association on some étale scheme chart. -/
theorem mem_weakAss_iff_existsEtaleWeakAss (F : X.Modules) [F.IsQuasicoherent]
    (x : Points X) :
    x ∈ F.weakAss ↔ existsEtaleWeakAss F x :=
  (existsEtaleWeakAss_iff_etaleStalkWeakAss F x).symm

end AlgebraicGeometry.AlgebraicSpace.Modules
