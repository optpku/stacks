/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.RingedSpace
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic

@[expose] public section

/-!
# Cohomology of pseudo-coherent derived modules on schemes

Pseudo-coherence of a derived module on a scheme controls the quasicoherence of its
cohomology sheaves.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.PseudoCoherent

variable {X : Scheme.{u}} {E : RingedSpace.ModuleDerived X.toRingedSpace} {m i : ℤ}

/-- The cohomology sheaves of an `m`-pseudo-coherent derived module in degrees strictly
above `m` are quasicoherent. -/
theorem higherCohomology_isQuasicoherent
    (hE : RingedSpace.ModuleDerived.IsMPseudoCoherent E m) (hi : m < i) :
    (RingedSpace.ModuleDerived.cohomologySheaf E i).IsQuasicoherent := sorry

/-- The degree-`m` cohomology sheaf of an `m`-pseudo-coherent derived module is a quotient
of a quasicoherent module. -/
theorem exists_quasicoherent_epi
    (hE : RingedSpace.ModuleDerived.IsMPseudoCoherent E m) :
    ∃ F : RingedSpace.QCoh X.toRingedSpace,
      ∃ f : F.obj ⟶ RingedSpace.ModuleDerived.cohomologySheaf E m, Epi f := sorry

/-- A pseudo-coherent derived module on a scheme has quasicoherent cohomology in every
degree. -/
theorem derivedQuasiCoherentModuleProperty
    (hE : RingedSpace.ModuleDerived.IsPseudoCoherent E) :
    DerivedCategory.cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) E := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.PseudoCoherent
