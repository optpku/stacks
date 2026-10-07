module

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials.Transitivity
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/- Lemma 29.32.9: the canonical sequence
`f^* Ω[Y/S] ⟶ Ω[X/S] ⟶ Ω[X/Y] ⟶ 0` is exact. -/
@[stacks 01UX] #check
  (AlgebraicGeometry.RingedSpace.Hom.Differentials.Transitivity.exact_and_epi
      f.toShHom g.toShHom :
    (AlgebraicGeometry.RingedSpace.Hom.Differentials.Transitivity.complex
      f.toShHom g.toShHom).Exact ∧
      Epi (AlgebraicGeometry.RingedSpace.Hom.Differentials.Transitivity.projection
        f.toShHom g.toShHom))

end AlgebraicGeometry
