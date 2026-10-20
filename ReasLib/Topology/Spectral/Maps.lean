/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.ConstructibleTopology.Maps
public import ReasLib.Topology.ConstructibleTopology.Specialization

/-!
# Homeomorphism Criteria for Spectral Maps

This module records a spectral-map criterion that promotes a bijective map to
a homeomorphism from either specialization-lifting or generalization-lifting.
-/

@[expose] public section

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [SpectralSpace X] [SpectralSpace Y] {f : X → Y}

namespace IsSpectralMap

/-- A bijective specializing spectral map between spectral spaces is a
homeomorphism. -/
@[stacks 09XU "specializing bijective spectral maps"]
theorem isHomeomorph_of_bijective_of_specializing
    (hf : IsSpectralMap f) (hf_bijective : Function.Bijective f)
    (hSpecializing : SpecializingMap f) :
    IsHomeomorph f := sorry

/-- A bijective generalizing spectral map between spectral spaces is a
homeomorphism. -/
@[stacks 09XU "generalizing bijective spectral maps"]
theorem isHomeomorph_of_bijective_of_generalizing
    (hf : IsSpectralMap f) (hf_bijective : Function.Bijective f)
    (hGeneralizing : GeneralizingMap f) :
    IsHomeomorph f := sorry

/-- Lemma 5.23.11: a bijective spectral map of spectral spaces is a
homeomorphism when it lifts specializations or generalizations. -/
@[stacks 09XU]
theorem isHomeomorph_of_bijective_of_specializing_or_generalizing
    (hf : IsSpectralMap f) (hf_bijective : Function.Bijective f)
    (hLift : SpecializingMap f ∨ GeneralizingMap f) :
    IsHomeomorph f := sorry

end IsSpectralMap
