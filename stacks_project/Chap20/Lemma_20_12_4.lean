/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Vanishing
import StacksCheckRecall

@[expose] public section

/- Lemma 20.12.4 (09SZ): if `ℱ` is a flasque `𝒪_X`-module, then its positive-degree Čech
cohomology vanishes on every indexed family of opens.  The module-level owner is the short
`ModuleCech` theorem in ReasLib; this chapter file is the source-facing labeled check surface.
-/

@[stacks 09SZ "flasque module vanishing predicate"]
#check @AlgebraicGeometry.RingedSpace.ModuleCech.isAcyclic_of_flasque

@[stacks 09SZ "degreewise flasque module Cech vanishing"]
#check @AlgebraicGeometry.RingedSpace.ModuleCech.isZero_of_flasque

@[stacks 01EV "Cech-acyclic module sheaves"]
#check @AlgebraicGeometry.RingedSpace.ModuleCech.IsAcyclic
