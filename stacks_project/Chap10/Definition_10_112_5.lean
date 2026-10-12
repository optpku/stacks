/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.Fiber.LocalQuotient
import StacksCheckRecall

/-!
# Local Rings of Fibers

@stack 00OL
-/

@[expose] public section

/- Definition 10.112.5 (Stacks tag `00OL`): for `q : PrimeSpectrum S` and
`p = q ∩ R`, `fiberLocalRingAt R S q` is the localization at `q` of the
residue-field fiber `S ⊗[R] p.ResidueField`. -/
@[stacks 00OL]
#check @fiberLocalRingAt

/- Canonical structural API for the local fiber ring, including the source
presentation `S_q / pS_q` and the closed-fiber presentation from the
localized map `R_p → S_q`. -/
#check @fiberPrimeAt
#check @toFiberLocalRingAt
#check @Algebra.Fiber.isScalarTower_residueField_localRingAt
#check @Algebra.Fiber.toLocalRingAt_comp_algebraMap
#check @Algebra.Fiber.localQuotientRingEquiv
#check @Algebra.Fiber.localClosedFiberAt
#check @Algebra.Fiber.localClosedFiberAtRingEquiv
#check @PrimeSpectrum.IsRegularInFiberLocalRing
