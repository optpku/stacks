/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.RingTheory.Henselian
import ReasLib.RingTheory.Henselian.SimpleRoot
import StacksCheckRecall

@[expose] public section

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R]

/- Definition 59.32.2: a commutative local ring is henselian when every monic
polynomial with a simple residue-field root lifts to a root in the ring. -/
@[stacks 03QF] #check
  (HenselianLocalRing.iff_monicSimpleRootLifting R :
    HenselianLocalRing R ↔
      (∀ polynomial : Polynomial R, polynomial.Monic →
        ∀ residueRoot : IsLocalRing.ResidueField R,
          Polynomial.aeval residueRoot polynomial = 0 →
          Polynomial.aeval residueRoot polynomial.derivative ≠ 0 →
          ∃ root : R, polynomial.IsRoot root ∧ IsLocalRing.residue R root = residueRoot))
