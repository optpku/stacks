module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Catenary.Basic
public import ReasLib.Topology.KrullDimension.Equidimensional

@[expose] public section

/-!
# Formally catenary local rings

This leaf owns formal catenarity as a property of a Noetherian local ring. The
completion quotient is kept in the defining field, so later catenary and
universal-catenary results can consume the condition without chapter imports.
@stack 0AW2
-/

open IsLocalRing

universe u

variable (A : Type u) [CommRing A]

/-- Definition 15.110.1 (current Stacks numbering: Definition 15.111.1, tag
`0AW2`): a Noetherian local ring is formally catenary when every minimal-prime
quotient of its maximal-ideal completion has equidimensional spectrum. -/
@[stacks 0AW2 "formal catenarity of a Noetherian local ring"]
class IsFormallyCatenaryRing : Prop extends IsLocalRing A, IsNoetherianRing A where
  /-- Equidimensionality of the completed quotient attached to a minimal prime. -/
  equidimensional_completion_quotient (p : minimalPrimes A) :
      TopologicalSpace.EquidimensionalSpace
        (PrimeSpectrum
          (AdicCompletion (maximalIdeal A) A ⧸
            Ideal.map (algebraMap A (AdicCompletion (maximalIdeal A) A)) p.1))

namespace IsFormallyCatenaryRing

/-- Definition 15.110.1 (`0AW2`) in explicit specification form: the class
contains the local and Noetherian assumptions together with equidimensionality
for every completed minimal-prime quotient. -/
@[stacks 0AW2 "formal catenarity specification"]
theorem iff [IsLocalRing A] [IsNoetherianRing A] :
    IsFormallyCatenaryRing A ↔
      ∀ p : minimalPrimes A,
        TopologicalSpace.EquidimensionalSpace
          (PrimeSpectrum
            (AdicCompletion (maximalIdeal A) A ⧸
              Ideal.map (algebraMap A (AdicCompletion (maximalIdeal A) A)) p.1)) := by
  constructor
  · exact fun h ↦ h.equidimensional_completion_quotient
  · exact fun h ↦
      { toIsLocalRing := inferInstance
        toIsNoetherian := inferInstance
        equidimensional_completion_quotient := h }
-- Proof strategy: unfold `IsFormallyCatenaryRing`; the forward direction is its
-- `equidimensional_completion_quotient` field, and the reverse direction builds the class
-- from the ambient local/Noetherian instances and the displayed family.

end IsFormallyCatenaryRing
