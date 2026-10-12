/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.AdjoinVariable.CellFamily
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

section Odd

variable {R : Type u} [CommRing R]
variable (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+)
variable (hd : Odd (d : ℕ))
variable (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1))
variable (hf : DividedPowerChainAlgebra.Adjoin.IsCycle A d f)

/- Lemma 23.6.8 (09PM) (1): the compatible differential on an odd-variable extension is realized
by the canonical divided-power chain-DGA cell adjoining `T` with `dT = f`. -/
@[stacks 09PM "(1), odd variable"]
#check (DividedPowerChainAlgebra.Adjoin.Odd.extension A d hd f hf :
  DividedPowerChainAlgebra.Adjoin.Odd.Extension A d f)
#check @DividedPowerChainAlgebra.Adjoin.Odd.gradedInclusion
#check @DividedPowerChainAlgebra.Adjoin.Odd.gradedPresentation
#check @DividedPowerChainAlgebra.Adjoin.Odd.cellGradedIso
#check @DividedPowerChainAlgebra.Adjoin.Odd.cellGradedPresentation
#check @DividedPowerChainAlgebra.Adjoin.Odd.family

end Odd

section Even

variable {R : Type u} [CommRing R]
variable (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+)
variable (hd : Even (d : ℕ))
variable (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1))
variable (hf : DividedPowerChainAlgebra.Adjoin.IsCycle A d f)

/- Lemma 23.6.8 (09PM) (2): the even-variable construction has the analogous divided-monomial
coefficient presentation and compatible chain differential. -/
@[stacks 09PM "(2), even variable"]
#check (DividedPowerChainAlgebra.Adjoin.Even.extension A d hd f hf :
  DividedPowerChainAlgebra.Adjoin.Even.Extension A d f)
#check @DividedPowerChainAlgebra.Adjoin.Even.gradedInclusion
#check @DividedPowerChainAlgebra.Adjoin.Even.gradedPresentation
#check @DividedPowerChainAlgebra.Adjoin.Even.cellGradedIso
#check @DividedPowerChainAlgebra.Adjoin.Even.cellGradedPresentation
#check @DividedPowerChainAlgebra.Adjoin.Even.family

end Even

#check @DividedPowerChainAlgebra.Adjoin.Cell.map_generator
#check @DividedPowerChainAlgebra.Adjoin.Cell.comparison
#check @DividedPowerChainAlgebra.Adjoin.Cell.comparisonIso
#check @DividedPowerChainAlgebra.Adjoin.Cell.existsUnique_comparison
#check @NonnegGradedAlgebra.Adjoin.Odd.CoefficientDifferential.map
#check @DividedPowerChainAlgebra.Adjoin.Odd.chainAlgebra
#check @DividedPowerChainAlgebra.Adjoin.Odd.inclusionChainHom
#check @DividedPowerChainAlgebra.Adjoin.Odd.inclusion
#check @DividedPowerChainAlgebra.Adjoin.Odd.inclusion_toChainHom
#check @DividedPowerChainAlgebra.Adjoin.Odd.inclusion_apply_ofNat
#check @DividedPowerChainAlgebra.Adjoin.Odd.generator
#check @DividedPowerChainAlgebra.Adjoin.Odd.liftChainHom
#check @DividedPowerChainAlgebra.Adjoin.Odd.lift
#check @DividedPowerChainAlgebra.Adjoin.Odd.lift_toChainHom
#check @DividedPowerChainAlgebra.Adjoin.Odd.lift_apply_ofNat
#check @DividedPowerChainAlgebra.Adjoin.Odd.cell
#check @DividedPowerChainAlgebra.Adjoin.Odd.cell_algebra
#check @DividedPowerChainAlgebra.Adjoin.Odd.cell_ι
#check @DividedPowerChainAlgebra.Adjoin.Odd.cell_generator
#check @DividedPowerChainAlgebra.Adjoin.Odd.cell_lift
#check @DividedPowerChainAlgebra.Adjoin.Odd.extension_toCell
#check @DividedPowerChainAlgebra.Adjoin.Odd.chainAlgebra_d_apply
#check @DividedPowerChainAlgebra.Adjoin.Even.chainAlgebra
#check @DividedPowerChainAlgebra.Adjoin.Even.inclusionChainHom
#check @DividedPowerChainAlgebra.Adjoin.Even.inclusion
#check @DividedPowerChainAlgebra.Adjoin.Even.inclusion_toChainHom
#check @DividedPowerChainAlgebra.Adjoin.Even.inclusion_apply_ofNat
#check @DividedPowerChainAlgebra.Adjoin.Even.generator
#check @DividedPowerChainAlgebra.Adjoin.Even.liftChainHom
#check @DividedPowerChainAlgebra.Adjoin.Even.lift
#check @DividedPowerChainAlgebra.Adjoin.Even.lift_toChainHom
#check @DividedPowerChainAlgebra.Adjoin.Even.lift_apply_ofNat
#check @DividedPowerChainAlgebra.Adjoin.Even.cell
#check @DividedPowerChainAlgebra.Adjoin.Even.cell_algebra
#check @DividedPowerChainAlgebra.Adjoin.Even.cell_ι
#check @DividedPowerChainAlgebra.Adjoin.Even.cell_generator
#check @DividedPowerChainAlgebra.Adjoin.Even.cell_lift
#check @DividedPowerChainAlgebra.Adjoin.Even.extension_toCell
#check @DividedPowerChainAlgebra.Adjoin.Even.chainAlgebra_d_apply
