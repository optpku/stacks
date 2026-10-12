/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.CycleGroup.FieldExtension.PerfectClosure

/-!
# Lemma 62.3.2

The field-extension pullback `Z_r(X) ⟶ Z_r(X_{k^perf})` is injective, and its
cokernel is a `p`-power torsion module.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.FieldExtension
open AlgebraicGeometry.SchemeOverField

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup.FieldExtension

variable {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
variable (X : SchemeOverField k) [Algebraic X] (r : ℕ)

/- Lemma 62.3.2 (1): the map `Z_r(X) ⟶ Z_r(X_{PerfectClosure k p})` is injective. -/
@[stacks 0H4G]
#check
  (AlgebraicGeometry.CycleGroup.FieldExtension.algebraicExtensionPullback_injective
      k (PerfectClosure k p) X r :
    Function.Injective (algebraicExtensionPullback k (PerfectClosure k p) X r))

/- Lemma 62.3.2 (2): the cokernel of the injective map `Z_r(X) ⟶
Z_r(X_{k^{perf}})` is a `p`-power torsion module. -/
@[stacks 0H4G] #check
  (AlgebraicGeometry.CycleGroup.FieldExtension.perfectClosure_coker_isIdealPowerTorsion
      p X r :
    Module.IsIdealPowerTorsion (principalIdeal (p : ℤ))
      (cycleGroup (Over.baseChange k (PerfectClosure k p) X) r ⧸
        (algebraicExtensionPullback k (PerfectClosure k p) X r).range))

end AlgebraicGeometry.CycleGroup.FieldExtension
