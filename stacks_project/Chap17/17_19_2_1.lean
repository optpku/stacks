/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaf.ExtensionByInitial.Presentation
import StacksCheckRecall

@[expose] public section

/- Equation 17.19.2.1 (0CAJ): finite basis presentations are precisely coequalizers of
maps between finite coproducts of finite-fibre lower-shriek constant sheaves. -/
@[stacks 0CAJ]
#check @TopCat.Sheaf.ExtensionByInitial.Constant.basisPresentation_iff_exists
