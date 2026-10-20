/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.FiniteEtalePurity
public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.Algebra.Regular.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic

@[expose] public section

open CategoryTheory
open IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
variable (f : maximalIdeal A)

/-- For a Noetherian local ring complete along a regular element of its maximal
ideal, purity descends to the principal quotient if its first two local
cohomology modules are finite over the ring, every maximal localization away
from the element satisfies purity, and the ring itself satisfies purity. -/
instance hasPurity_principalQuotient_of_complete_localCohomology
    [IsAdicComplete (principalIdeal (f : A)) A]
    [Fact (IsRegular (f : A))]
    [Module.Finite A
      ((localCohomology (maximalIdeal A) 1).obj
        (ModuleCat.of A (A ⧸ principalIdeal (f : A))))]
    [Module.Finite A
      ((localCohomology (maximalIdeal A) 2).obj
        (ModuleCat.of A (A ⧸ principalIdeal (f : A))))]
    [Fact (hasPurityAtMaximalsAway f)]
    [HasPurity A] :
    HasPurity (A ⧸ principalIdeal (f : A)) := sorry

/-- For a Noetherian local ring admitting a dualizing complex and complete along
an element of its maximal ideal, purity descends to the principal quotient if
every maximal localization away from the element and the ring itself satisfy
purity, and either the localization away from the element satisfies `(S₂)` with
every minimal component not containing the element of dimension at least four,
or every prime outside its zero locus whose closure meets that locus beyond the
closed point has depth plus quotient dimension greater than three. -/
instance hasPurity_principalQuotient_of_dualizing_complete
    [Fact (∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizing)]
    [IsAdicComplete (principalIdeal (f : A)) A]
    [Fact (dualizingCompleteNeighborhoodAlternative f)]
    [Fact (hasPurityAtMaximalsAway f)]
    [HasPurity A] :
    HasPurity (A ⧸ principalIdeal (f : A)) := sorry

end AlgebraicGeometry.PuncturedSpectrum
