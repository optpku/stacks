module

import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Exact
import StacksCheckRecall

open CategoryTheory

noncomputable section

universe u

variable {X : AlgebraicGeometry.Scheme.{u}}
variable (ℒ : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible ℒ]
variable (s : ℒ.sections) [AlgebraicGeometry.RingedSpace.IsRegularSection ℒ s]
variable (D : X.IdealSheafData)
  [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]

/- Remark 31.14.11: a regular section of an invertible module sheaf cuts out an effective
Cartier divisor. -/
@[stacks 0C6K] #check
  (AlgebraicGeometry.Scheme.instIsEffectiveCartierDivisorZeroScheme ℒ s :
    AlgebraicGeometry.IsEffectiveCartierDivisor
      (AlgebraicGeometry.Scheme.zeroSchemeι ℒ s))

/- The section map and restriction to the zero scheme form a short exact complex. -/
#check
  (AlgebraicGeometry.Scheme.zeroSchemeRestrictionSequence_shortExact ℒ s :
    (AlgebraicGeometry.Scheme.zeroSchemeRestrictionSequence ℒ s).ShortExact)

/- The dual-section map and the structure sheaf of the zero scheme form a short exact
complex. -/
#check
  (AlgebraicGeometry.Scheme.zeroSchemeStructureSheafSequence_shortExact ℒ s :
    (AlgebraicGeometry.Scheme.zeroSchemeStructureSheafSequence ℒ s).ShortExact)

/- The canonical section of an effective Cartier divisor and restriction to its normal sheaf
form a short exact complex. -/
#check
  (AlgebraicGeometry.Scheme.IdealSheafData.normalSheafSequence_shortExact D :
    (AlgebraicGeometry.Scheme.IdealSheafData.normalSheafSequence D).ShortExact)

/- The ideal sheaf of an effective Cartier divisor and its structure-sheaf quotient form a
short exact complex. -/
#check
  (AlgebraicGeometry.Scheme.IdealSheafData.structureSheafSequence_shortExact D :
    (AlgebraicGeometry.Scheme.IdealSheafData.structureSheafSequence D).ShortExact)
