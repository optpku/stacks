module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.ModuleCech

import StacksCheckRecall

/-!
# The principal-adic module Cech sequence

This is the specialization of the module Beauville-Laszlo Cech sequence to the principal-adic
completion map.

@stack 0BNV
-/

universe u

open CategoryTheory

section

variable {R : Type u} [CommRing R]
variable (M : Type u) [AddCommGroup M] [Module R M]
variable (f : R)

-- 15.91.9.2: specialize the displayed module Cech sequence to `R^`.
@[stacks 0BNV "15.91.9.2"]
#check
  (beauvilleLaszloModuleCechSequence (principalAdicCompletion f) M f :
    ShortComplex (ModuleCat R))

end
