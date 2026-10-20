/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.LinearAlgebra.LinearMap.Frobenius
import StacksCheckRecall

@[expose] public section

universe u v

namespace LinearMap.Frobenius

variable {k : Type u} {V : Type v} {p : ℕ}
variable [Field k] [IsAlgClosed k] [Fact p.Prime] [CharP k p]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/- Lemma 59.63.2 -/
@[stacks 0A3L] #check
  (LinearMap.Frobenius.subId_surjective :
    (F : V →ₛₗ[_root_.frobenius k p] V) → Function.Surjective (LinearMap.Frobenius.subId F))

#check
  (LinearMap.Frobenius.kerFiniteDimensional :
    (F : V →ₛₗ[_root_.frobenius k p] V) →
      FiniteDimensional (ZMod p) (LinearMap.Frobenius.subId F).ker)

#check
  (LinearMap.Frobenius.kerFinrankLe :
    (F : V →ₛₗ[_root_.frobenius k p] V) →
      Module.finrank (ZMod p) (LinearMap.Frobenius.subId F).ker ≤ Module.finrank k V)

end LinearMap.Frobenius
