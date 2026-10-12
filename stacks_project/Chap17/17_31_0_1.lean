/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent
import StacksCheckRecall

@[expose] public section

/- Equation 17.31.0.1 (08TH): the canonical polynomial presentation evaluates every bracket
generator at the section which labels it. -/
@[stacks 08TH]
#check @CategoryTheory.Sheaf.FreeAlgebra.Presentation.generator_map

#check @CategoryTheory.Sheaf.FreeAlgebra.Presentation.map
