/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap97.«97_6_0_1_Lifting»
import StacksCheckRecall

@[expose] public section

/- 97.6.0.1: for a 1-morphism `p : X ⟶ Y` of categories fibred in groupoids
over `(Sch/S)_fppf`, a solution `(x', β, γ')` to an infinitesimal lifting
problem makes the square with top arrow `γ'|_U = restrictHom p i γ'`, left
arrow `p(β) = β.hom ▷ p`, bottom arrow `γ`, and right arrow the identity on
`y'|_U = slice.pullback i y'` commute. -/
@[stacks 06D0] #check AlgebraicGeometry.Groupoids.Hom.FormallySmoothOnObjects.restrictionSquare
