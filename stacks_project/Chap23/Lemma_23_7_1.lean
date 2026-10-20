/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.SquareZeroLift
import StacksCheckRecall

@[expose] public section

/-!
# Obstructions from lifted differentials over square-zero extensions

The reusable owner separates the canonical quotient `A.annihilatorQuotient` from a noncanonical
`SquareZeroLift`.  A lift determines the degree-`-2` obstruction derivation, while finite freeness
supplies the source-facing existence theorem.
-/

/- The reusable layer first exposes the explicit lift owner and its canonical obstruction. -/
#check @DividedPowerChainAlgebra.SquareZeroLift
#check @DividedPowerChainAlgebra.SquareZeroLift.nonempty_of_finite
#check @DividedPowerChainAlgebra.annihilatorQuotient
#check @DividedPowerChainAlgebra.SquareZeroLift.obstruction
#check @DividedPowerChainAlgebra.SquareZeroLift.chainObstructionMap
#check @DividedPowerChainAlgebra.SquareZeroLift.chainObstruction
#check @DividedPowerChainAlgebra.SquareZeroLift.chainObstruction_toHomogeneousMap
#check @DividedPowerChainAlgebra.SquareZeroLift.chainObstruction_apply
#check @DividedPowerChainAlgebra.SquareZeroLift.obstructionHomologyMap

/- Lemma 23.7.1 (Tag 09PS): the source existential follows from the explicit lift API. -/
open RingHom.SquareZeroExtension

universe u v w

section

variable {R' R : Type u} [CommRing R'] [CommRing R]
variable {f : R' →+* R} [f.IsSquareZeroExtension]
variable {generators : ℕ → Type v}
variable {A : DividedPowerChainAlgebra.{u, w} R}
variable {g : RingHom.SquareZeroExtension.Generator f}
variable {P : A.toGradedAlgebra.FreePresentation generators}
variable (h_finite : ∀ n : ℕ, Finite (generators n))

@[stacks 09PS "Lemma 23.7.1"]
#check (DividedPowerChainAlgebra.SquareZeroLift.exists_obstruction_of_finite
    A g P h_finite :
  ∃ (L : A.SquareZeroLift g P)
    (θ : ChainGradedAlgebra.Derivation
      (A.toGradedAlgebra.toChainGradedAlgebra.quotientByIdeal
        (kernelAnnihilator f)) (-2)),
    θ = L.obstruction.toDerivation)

end
