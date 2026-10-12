/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Regular.RingMap

@[expose] public section

namespace Algebra

universe u v

section

variable {R : Type u} {Λ : Type v}
variable [CommRing R] [CommRing Λ] [Algebra R Λ]

/- The reusable owner of regular ring maps. -/
#check @RingHom.Regular
#check @RingHom.Regular.iff_flat_and_geometricallyRegular_fiber

/- Situation 16.8.1: Here `R → Λ` is a regular ring map of Noetherian rings. -/
@[stacks 07F2] #check
  fun (_ : IsNoetherianRing R) (_ : IsNoetherianRing Λ)
    (_ : (algebraMap R Λ).Regular) ↦
    (algebraMap R Λ).Regular

end

end Algebra
