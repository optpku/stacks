/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Square
public import stacks_project.Chap91.Situation_91_9_1_Comparison
import StacksCheckRecall

/- 91.9.1.1: a morphism of thickenings of ringed topoi `(f, f')` is given by the
commutative square of morphisms of ringed topoi with vertices
`(Sh(C), O)`, `(Sh(D), O')`, `(Sh(B), O_B)`, `(Sh(B'), O_{B'})`, whose horizontal
arrows are thickenings. This is assembled by `homMk`, with `upper = i`,
`left = f`, `right = f'`, `lower = t`, and `cell : TwoIso (comp i f') (comp f t)`. -/
@[stacks 08M8] #check @RingedSite.ToposHom.Thickening.homMk
