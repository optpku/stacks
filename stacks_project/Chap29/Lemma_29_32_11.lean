/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Differentials.Product
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/- Lemma 29.32.11: the two canonical projection comparisons identify the relative
differentials of a fiber product with the direct sum of the pulled-back relative
differentials of its factors. -/
@[stacks 01V1] #check
  (AlgebraicGeometry.Scheme.RelativeDifferentials.Product.comparison_isIso f g :
    IsIso
      (AlgebraicGeometry.Scheme.RelativeDifferentials.Product.comparison f g :
        ((RingedSpace.Hom.pullback (pullback.fst f g).toShHom).obj Ω[f.toShHom] ⊞
          (RingedSpace.Hom.pullback (pullback.snd f g).toShHom).obj Ω[g.toShHom]) ⟶
            Ω[(pullback.snd f g ≫ g).toShHom]))

end AlgebraicGeometry
