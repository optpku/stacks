/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.NumberTheory.Padics.SquareCubeQuotient

/- Example 42.68.11: after identifying the residue field of `ℤ_[p]` with `ZMod p`,
the finite-length determinant of the block endomorphism `((a, b), (p * c, d))` is the
reduction of the unit `a ^ 2 * d ^ 3`. -/
@[stacks 02PE] #check
  (PadicInt.finiteLengthDeterminant_squareCubeBlockEnd :
    ∀ (p : ℕ) [Fact p.Prime] (a : ℤ_[p]ˣ) (b c : ℤ_[p]) (d : ℤ_[p]ˣ),
      PadicInt.residueField
          ((PadicInt.squareCubeBlockEnd p a b c d).finiteLengthDeterminant
            (PadicInt.squareCubeQuotient_isFiniteLength p)) =
        (Units.map PadicInt.toZMod.toMonoidHom (a ^ 2 * d ^ 3)).val)
