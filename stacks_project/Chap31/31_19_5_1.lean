/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.NormalCone.Comparison

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
variable (P : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver P]
variable (Q : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf i)))
variable [IsRelativeSpectrumOver Q]

/- 31.19.5.1: The normal cone of an immersion maps canonically to its normal bundle. -/
@[stacks 0637] #check (AlgebraicGeometry.Scheme.normalConeToNormalBundle i P Q :
  AlgebraicGeometry.Scheme.normalCone i P ⟶
    AlgebraicGeometry.Scheme.normalBundle i Q)

end AlgebraicGeometry.Scheme
