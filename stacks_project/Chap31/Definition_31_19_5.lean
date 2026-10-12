/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.NormalCone

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

section NormalCone

variable (P : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver P]

/- Definition 31.19.5 (1): The normal cone of an immersion `i : Z ⟶ X` is the relative
spectrum over `Z` of the total conormal algebra. -/
@[stacks 0636]
#check (AlgebraicGeometry.Scheme.normalCone_eq_relativeSpec i P :
  AlgebraicGeometry.Scheme.normalCone i P = AlgebraicGeometry.Scheme.relativeSpec P)

end NormalCone

section NormalBundle

variable (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf i)))
variable [IsRelativeSpectrumOver P]

/- Definition 31.19.5 (2): The normal bundle of an immersion `i : Z ⟶ X` is the relative
spectrum over `Z` of the symmetric algebra of its conormal sheaf. -/
@[stacks 0636]
#check (AlgebraicGeometry.Scheme.normalBundle_eq_relativeSpec i P :
  AlgebraicGeometry.Scheme.normalBundle i P = AlgebraicGeometry.Scheme.relativeSpec P)

end NormalBundle

end AlgebraicGeometry.Scheme
