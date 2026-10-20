module

import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Quasicoherent
import StacksCheckRecall

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry

universe u

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/- Definition 29.31.1: The conormal sheaf of an immersion `i : Z ⟶ X` is the
`Z.Modules` object obtained from the kernel ideal as `I / I ^ 2`. -/
@[stacks 01R2] #check
  (AlgebraicGeometry.Scheme.Hom.conormalSheaf i : AlgebraicGeometry.Scheme.Modules Z)

/- The conormal sheaf of an immersion is quasi-coherent. -/
#check
  (AlgebraicGeometry.Scheme.Hom.conormalSheaf_isQuasicoherent i :
    (AlgebraicGeometry.Scheme.Hom.conormalSheaf i).IsQuasicoherent)

end AlgebraicGeometry
