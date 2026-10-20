module

public import ReasLib.AlgebraicGeometry.Polarized.ToSpaces
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic

/-!
# Groupoid fibrations of polarized proper schemes

The category of polarized proper schemes is fibred in groupoids over proper flat
finitely presented algebraic-space families and over schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces hiding p

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- The forgetful functor from polarized proper schemes to proper flat finitely
presented algebraic-space families is fibred in groupoids. -/
@[stacks 0D3Z]
instance instIsFiberedInGroupoids_toFpFlatProper :
    Functor.IsFibered.InGroupoids toFpFlatProper :=
  sorry

/-- The base-scheme functor of polarized proper schemes is fibred in groupoids. -/
@[stacks 0D3Z]
instance instIsFiberedInGroupoids : Functor.IsFibered.InGroupoids p :=
  sorry

/-- The base-scheme functor of polarized proper schemes, viewed over `Spec ℤ`,
is fibred in groupoids. -/
instance instIsFiberedInGroupoids_toOverSpecZ :
    Functor.IsFibered.InGroupoids (p ⋙ schemeToOverSpecZ) :=
  sorry

/-- Polarized proper schemes, bundled as a category fibred in groupoids over schemes. -/
def toGroupoids : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} Scheme.{u} :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u} p

/-- The projection of the bundled category of polarized proper schemes is its
base-scheme functor. -/
theorem toGroupoids_p : toGroupoids.p = p :=
  rfl

/-- Polarized proper schemes, bundled as a category fibred in groupoids over
schemes over `Spec ℤ`. -/
def toGroupoidsOverSpecZ : GroupoidsOver specZ :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u} (p ⋙ schemeToOverSpecZ)

/-- The projection of the bundled category of polarized proper schemes over
`Spec ℤ` is its base-scheme functor followed by the canonical functor to the slice. -/
theorem toGroupoidsOverSpecZ_p :
    toGroupoidsOverSpecZ.p = p ⋙ schemeToOverSpecZ :=
  rfl

end AlgebraicGeometry.Polarized
