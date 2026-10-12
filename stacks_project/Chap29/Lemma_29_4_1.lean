/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.ClosedImmersion
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/- Lemma 29.4.1: for a closed immersion `i : Z ⟶ X`, pushforward on quasicoherent
modules is exact and fully faithful, with essential image the modules annihilated by the
ideal sheaf cutting out `Z`. -/
@[stacks 01QY] #check
  (Scheme.QCoh.pushforwardExact (i := i) :
    exactFunctor (Scheme.QCoh Z) (Scheme.QCoh X) (Scheme.QCoh.pushforward i))

#check
  (Scheme.QCoh.pushforward i : Scheme.QCoh Z ⥤ Scheme.QCoh X)

#check
  (Scheme.QCoh.pushforward_map_bijective (i := i) :
    ∀ F G : Scheme.QCoh Z,
      Function.Bijective (fun f : F ⟶ G ↦ (Scheme.QCoh.pushforward i).map f))

#check
  (Scheme.QCoh.mem_essImage_iff_idealSheaf_smul_eq_zero (i := i) :
    ∀ G : Scheme.QCoh X,
      (Scheme.QCoh.pushforward i).essImage G ↔
        ∀ U : X.Opens,
          ∀ s : (RingedSpace.Hom.idealSheaf i.toShHom).val.obj (op U),
            ∀ m : G.obj.val.obj (op U),
              ((RingedSpace.Hom.idealSheafι i.toShHom).val.app (op U) s) • m = 0)

end AlgebraicGeometry
