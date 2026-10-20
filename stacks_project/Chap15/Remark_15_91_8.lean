module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.Flat

import StacksCheckRecall

/-!
# Flat principal-adic completion and glueing

The finite torsion comparison and the resulting Beauville-Laszlo glueing-pair statements are
owned by `ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.Flat`.

@stack 0BNT
-/

universe u

open LocalizedModule.Away.BeauvilleLaszlo

section

variable {R : Type u} [CommRing R]
variable (f : R) (n : ℕ+)
variable (hflat : (algebraMap R (principalAdicCompletion f)).Flat)

-- Remark 15.91.8 (1): flat completion preserves every positive finite torsion stage.
@[stacks 0BNT "Remark 15.91.8 (1)"]
#check
  (principalAdicCompletionTorsionByMap_bijective_of_flat f hflat n :
    Function.Bijective (principalAdicCompletionTorsionByMap f n))

-- Remark 15.91.8 (2): flat completion therefore gives a glueing pair.
@[stacks 0BNT "Remark 15.91.8 (2)"]
#check
  (principalAdicCompletion_isGlueingPair_of_flat f hflat :
    IsBeauvilleLaszloGlueingPairAlong
      (algebraMap R (principalAdicCompletion f)) f)

section

variable [IsNoetherianRing R]

-- Remark 15.91.8 (3): the finite-stage comparison applies in the Noetherian case.
@[stacks 0BNT "Remark 15.91.8 (3)"]
#check
  (principalAdicCompletionTorsionByMap_bijective_of_isNoetherianRing f n :
    Function.Bijective (principalAdicCompletionTorsionByMap f n))

-- Remark 15.91.8 (4): in particular, every Noetherian ring gives this glueing pair.
@[stacks 0BNT "Remark 15.91.8 (4)"]
#check
  (principalAdicCompletion_isGlueingPair_of_isNoetherianRing f :
    IsBeauvilleLaszloGlueingPairAlong
      (algebraMap R (principalAdicCompletion f)) f)

end

end
