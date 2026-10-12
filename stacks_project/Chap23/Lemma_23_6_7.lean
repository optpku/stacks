/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.BaseChange.Unit
import StacksCheckRecall

@[expose] public section

universe uR uR' uA

section

variable {R : Type uR} {R' : Type uR'}
variable [CommRing R] [CommRing R'] [Algebra R R']
variable (A : DividedPowerChainAlgebra.{uR, uA} R)

/- Lemma 23.6.7 (09PL): a compatible divided-power chain DGA admits scalar extension, with
degreewise tensor-product identifications and the expected differential and divided-power formulas.
Every supplied model also carries the explicit semilinear unit `x ↦ 1 ⊗ₜ x`; this construction
does not select a model from the existence statement.
-/
@[stacks 09PL]
#check (DividedPowerChainAlgebra.nonemptyBaseChange (R' := R') A :
  Nonempty (DividedPowerChainAlgebra.BaseChange (R' := R') A))

end

#check @DividedPowerChainAlgebra.BaseChange
#check @DividedPowerChainAlgebra.BaseChange.dpComparison
#check @DividedPowerChainAlgebra.BaseChange.chainComparison
#check @DividedPowerChainAlgebra.BaseChange.comparisonIso
#check @DividedPowerChainAlgebra.BaseChange.unit
#check @DividedPowerChainAlgebra.BaseChange.unit_apply_ofNat
#check @DividedPowerChainAlgebra.BaseChange.unit_gammaPiece
#check @DividedPowerChainAlgebra.BaseChange.chainComparison_unit_apply
