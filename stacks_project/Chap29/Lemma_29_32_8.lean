module

import Mathlib.AlgebraicGeometry.Scheme
import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Differentials
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X X' S S' : Scheme.{u}}
variable (f : X' ⟶ X) (g : S' ⟶ S) (h : X ⟶ S) (h' : X' ⟶ S')
variable (sq : CommSq f h' h g)

/- Lemma 29.32.8: a commutative square of schemes determines a unique pullback comparison
morphism on relative differentials, characterized by its action on universal differentials. -/
@[stacks 01UV] #check
  (AlgebraicGeometry.RingedSpace.Hom.Differentials.existsUnique_comparison
      (sq.map
        (Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToSheafedSpace)) :
    ∃! τ : (RingedSpace.Hom.pullback f.toShHom).obj Ω[h.toShHom] ⟶ Ω[h'.toShHom],
      AlgebraicGeometry.RingedSpace.Hom.Differentials.IsComparison τ)

#check
  (AlgebraicGeometry.RingedSpace.Hom.Differentials.comparisonDerivation
      (sq.map
        (Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToSheafedSpace)) :
    RingedSpace.Hom.derivations h.toShHom
      ((RingedSpace.Hom.pushforward f.toShHom).obj Ω[h'.toShHom]))

#check
  (AlgebraicGeometry.RingedSpace.Hom.Differentials.comparison
      (sq.map
        (Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToSheafedSpace)) :
    (RingedSpace.Hom.pullback f.toShHom).obj Ω[h.toShHom] ⟶ Ω[h'.toShHom])

end AlgebraicGeometry
