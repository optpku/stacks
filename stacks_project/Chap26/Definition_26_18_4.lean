/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (s : S)

/- Definition 26.18.4: the scheme-theoretic fiber of `f` over `s` is the canonical pullback
scheme `f.fiber s`, namely `pullback f (S.fromSpecResidueField s)`. -/
@[stacks 01K0] #check f.fiber s

#check f.fiberι s
@[stacks 01K0 "fiber as a scheme over the residue field"]
#check f.fiberOverSpecResidueField s
#check f.fiberToSpecResidueField s

end AlgebraicGeometry
