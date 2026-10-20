/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Cohomology

@[expose] public section

/-!
# Pseudo-coherent complexes on Noetherian schemes

On a Noetherian scheme, pseudo-coherence is characterized by bounded-above coherent
cohomology.
-/

open CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

variable {X : Scheme.{u}} [IsNoetherian X]

/-- An object with quasicoherent cohomology on a Noetherian scheme is `m`-pseudo-coherent
if and only if it is bounded above and its cohomology sheaves in degrees at least `m` are
coherent. -/
theorem isMPseudoCoherent_iff_boundedAbove_and_cohomology_coherent_ge
    (E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) (m : ℤ) :
    RingedSpace.ModuleDerived.IsMPseudoCoherent E.obj m ↔
      (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj ∧
        ∀ i : ℤ, m ≤ i →
          (RingedSpace.ModuleDerived.cohomologySheaf E.obj i).IsCoherent := sorry

/-- An object with quasicoherent cohomology on a Noetherian scheme is pseudo-coherent
if and only if it is bounded above and all of its cohomology sheaves are coherent. -/
theorem isPseudoCoherent_iff_boundedAbove_and_cohomology_coherent
    (E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) :
    RingedSpace.ModuleDerived.IsPseudoCoherent E.obj ↔
      (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj ∧
        DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) E.obj := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
