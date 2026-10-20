module

public import ReasLib.RingTheory.Noetherian.ULift
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Effective
public import ReasLib.AlgebraicGeometry.Polarized.Groupoids
public import ReasLib.AlgebraicGeometry.Polarized.FormalSystem.Algebraization

/-!
# Effectiveness of polarized formal objects

Every Artin formal object of the stack of polarized proper schemes over
`specZ` is effective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- Every Artin formal object of the stack of polarized proper schemes over
`specZ` is effective. -/
@[stacks 0D4U]
instance instFormalObjectIsEffective (ξ : FormalObject toGroupoidsOverSpecZ) :
    FormalObject.IsEffective ξ :=
  sorry

/-- Every formal object of polarized proper schemes over `specZ` is isomorphic
to the approximation of some complete local object. -/
theorem exists_completeLocalObject (ξ : FormalObject toGroupoidsOverSpecZ) :
    ∃ x : CompleteLocalObject toGroupoidsOverSpecZ,
      Nonempty ((approximation toGroupoidsOverSpecZ).obj x ≅ ξ) :=
  sorry

end AlgebraicGeometry.Polarized
