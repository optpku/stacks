/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Regular.GRing.EssentialFiniteness
import StacksCheckRecall

/-!
# Proposition 15.50.10

@stack 07PV
-/

@[expose] public section

/- Proposition 15.50.10, tag `07PV`: an essentially finite type algebra over a G-ring is a
G-ring. -/
@[stacks 07PV "essentially finite type extension of a G-ring"]
#check @IsGRing.of_essFiniteType
