/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Affine
import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Finite
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

section HigherDirectImage

variable
    (f : X ⟶ Y) [IsFinite f] [IsLocallyNoetherian Y]
    [HasInjectiveResolutions X.Modules]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (p : ℕ) (hp : 0 < p)

/-
Lemma 30.9.9

For a finite morphism to a locally Noetherian scheme, the positive higher direct images of a
quasi-coherent module vanish.
-/
@[stacks 01Y6] #check
  (AlgebraicGeometry.Scheme.higherDirectImageModule_isZero_of_isAffineHom f ℱ p hp :
    IsZero (((Scheme.Modules.pushforward f).rightDerived p).obj ℱ))

end HigherDirectImage

section CoherentPushforward

variable
    (f : X ⟶ Y) [IsFinite f] [IsLocallyNoetherian Y]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsCoherent]

#check
  (AlgebraicGeometry.Scheme.Modules.pushforward_obj_isCoherent_of_isFinite f ℱ :
    ((Scheme.Modules.pushforward f).obj ℱ).IsCoherent)

end CoherentPushforward

end AlgebraicGeometry.Scheme.Modules
