/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.ClosedImmersion

/-!
# Cohomology of relatively pseudo-coherent derived modules on schemes

Relative pseudo-coherence over a locally finite type morphism controls the quasicoherence
of the cohomology sheaves of a derived module.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

namespace IsMPseudoCoherentOver

variable {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
variable {E : RingedSpace.ModuleDerived X.toRingedSpace} {m i : ℤ}

/-- The cohomology sheaves of a relatively `m`-pseudo-coherent derived module in degrees
strictly above `m` are quasicoherent. -/
theorem higherCohomology_isQuasicoherent
    (hE : IsMPseudoCoherentOver f E m) (hi : m < i) :
    (RingedSpace.ModuleDerived.cohomologySheaf E i).IsQuasicoherent := sorry

end IsMPseudoCoherentOver

namespace IsPseudoCoherentOver

variable {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
variable {E : RingedSpace.ModuleDerived X.toRingedSpace}

/-- A relatively pseudo-coherent derived module has quasicoherent cohomology in every
degree. -/
theorem derivedQuasiCoherentModuleProperty
    (hE : IsPseudoCoherentOver f E) :
    Scheme.derivedQuasiCoherentModuleProperty X E := sorry

end IsPseudoCoherentOver

end AlgebraicGeometry.Scheme.ModuleDerived
