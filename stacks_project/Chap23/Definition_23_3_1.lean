/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.Category
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open DividedPowers

universe u

/- Definition 23.3.1 (07GU): a divided power ring is the canonical bundled commutative ring,
ideal, and divided-power structure. -/
@[stacks 07GU] #check (DividedPowerRing.{u} : Type (u + 1))

/- Its morphisms are supplied by the canonical `DividedPowerRing` category structure. -/
#check @DividedPowerRing.of
#check @DividedPowerRing.ofHom
