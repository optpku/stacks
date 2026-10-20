module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Polarized.FormalEffectiveness

/-!
# Lemma 99.14.12

The stack Polarized over `specZ` has every Artin formal object effective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/- Lemma 99.14.12: Every Artin formal object of the stack Polarized over
`specZ` is effective. -/
@[stacks 0D4U] #check
  (AlgebraicGeometry.Polarized.instFormalObjectIsEffective :
    ∀ (ξ : FormalObject toGroupoidsOverSpecZ.{u}), FormalObject.IsEffective ξ)

#check
  (AlgebraicGeometry.Polarized.exists_completeLocalObject :
    ∀ (ξ : FormalObject toGroupoidsOverSpecZ.{u}),
      ∃ x : CompleteLocalObject toGroupoidsOverSpecZ.{u},
        Nonempty ((approximation toGroupoidsOverSpecZ.{u}).obj x ≅ ξ))

end AlgebraicGeometry.Polarized
