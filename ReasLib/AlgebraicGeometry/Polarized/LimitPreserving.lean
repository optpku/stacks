module

public import ReasLib.AlgebraicGeometry.Polarized.Groupoids
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreserving

/-!
# Limit preservation of polarized proper schemes

The category fibred in groupoids of polarized proper schemes is limit preserving
over schemes over `Spec ℤ`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Polarized

/-- The category fibred in groupoids of polarized proper schemes over `Spec ℤ`
is limit preserving. -/
@[stacks 0D43]
instance instLimitPreserving :
    AlgebraicGeometry.Groupoids.LimitPreserving toGroupoidsOverSpecZ.{u} :=
  sorry

end AlgebraicGeometry.Polarized
