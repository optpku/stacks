/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_3_1_Separation
import StacksCheckRecall

@[expose] public section

/- Definition 66.3.1 (1): an algebraic space `X` over a scheme `S` is separated if
`extendBaseTerminal X` is separated, equivalently if `diag (extendBaseTerminal X)` is a
closed immersion. -/
@[stacks 03BS] #check AlgebraicGeometry.AlgebraicSpace.IsAbsolutelySeparated

/- Definition 66.3.1 (2): an algebraic space `X` over a scheme `S` is locally separated if
`extendBaseTerminal X` is locally separated, equivalently if `diag (extendBaseTerminal X)` is
an immersion. -/
@[stacks 03BS] #check AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyLocallySeparated

/- Definition 66.3.1 (3): an algebraic space `X` over a scheme `S` is quasi-separated if
`extendBaseTerminal X` is quasi-separated, equivalently if `diag (extendBaseTerminal X)` is
quasi-compact. -/
@[stacks 03BS] #check AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated

/- Definition 66.3.1 (4): an algebraic space `X` over a scheme `S` is Zariski locally
quasi-separated if `extendBaseTerminal X` admits a Zariski covering by quasi-separated open
subspaces. -/
@[stacks 03BS] #check AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyZariskiLocallyQuasiSeparated
