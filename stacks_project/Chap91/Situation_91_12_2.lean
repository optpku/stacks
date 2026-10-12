/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.Situation_91_12_2_Diagram
import StacksCheckRecall

/- Situation 91.12.2: let `f : (Sh(C), O) ⟶ (Sh(B), O_B)` be a morphism of
ringed topoi. Consider a commutative square of first-order thickenings whose
top arrow `h` is a morphism of first-order thickenings of `(Sh(C), O)`, whose
bottom arrow is a morphism of first-order thickenings of `(Sh(B), O_B)`, each
`f'_i` restricts to `f`, both pairs `(f, f'_i)` are strict morphisms of
thickenings, both `f'_i` are flat, and `F` is an `O`-module flat over `O_B`.
After identifying underlying topoi, this is `FlatMorphismSquare`. -/
@[stacks 0CYD] #check @SheafOfModules.RingedSite.FirstOrderThickening.FlatMorphismSquare
