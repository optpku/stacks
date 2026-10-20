/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.IdealPower.Hom
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension

@[expose] public section

open scoped BigOperators

universe u

namespace Ideal.LocalCohomology

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- A finitely generated ideal of local-cohomological dimension one has a power whose
inclusion into the ambient ring is a finite weighted sum of maps from that power. -/
theorem existsPowerInclusionLift {r : ℕ} (I : Ideal A) (f : Fin r → A)
    (hgen : Ideal.span (Set.range f) = I)
    (hcd : dimension I I.fg_of_isNoetherianRing = 1) :
    ∃ c : ℕ, 1 ≤ c ∧ ∃ φ : Fin r → I.powerHom A c,
      ∑ j, f j • φ j = (I ^ c).subtype := sorry

end Ideal.LocalCohomology
