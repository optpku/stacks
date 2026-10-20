/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Sections.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.SequentialInverseSystem
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/- Lemma 52.17.2: if the inverse system `H⁰(S.U, Fₙ)` has the Mittag-Leffler
property, then every canonical map from the restriction of
`(sectionsLimit S F / S.I ^ n sectionsLimit S F)˜` to `Fₙ` is an epimorphism. -/
@[stacks 0EHF]
#check (AlgebraicGeometry.Scheme.CoherentFormalModules.sectionsComparison_epi :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)),
    IsMittagLeffler (sectionsSystem S F) →
      ∀ n : ℕ, Epi (sectionsComparison S F n))

end AlgebraicGeometry.Scheme.CoherentFormalModules
