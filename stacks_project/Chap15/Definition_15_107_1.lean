/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.LocalRing.Unibranch

/-!
# Definition 15.107.1

@stack 0BPZ
-/

@[expose] public section

/- Definition 15.107.1 (1), tag `0BPZ`: a local ring is unibranch when its
reduction is a domain and the normalization of that reduction is local. -/
@[stacks 0BPZ "unibranch local rings"]
#check @IsUnibranch

/- Definition 15.107.1 (2), tag `0BPZ`: a local ring is geometrically
unibranch when it is unibranch and the induced residue-field extension is
purely inseparable. -/
@[stacks 0BPZ "geometrically unibranch local rings"]
#check @IsGeometricallyUnibranch
