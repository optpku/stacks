/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Basic

/-!
# Projective space as a projective bundle

The canonical relative projective space represents the projective bundle of the standard free
module.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- The canonical projection from projective `n`-space over `S` admits a projective-bundle
representation for the standard free module of rank `n + 1`. -/
theorem toBase_hasProjectiveBundleRepresentation (S : Scheme.{u}) (n : ℕ) :
    Nonempty
      (Scheme.ProjectiveBundle.Representation (toBase n S)
        (SheafOfModules.freeFin (n + 1))) := sorry

end AlgebraicGeometry.ProjectiveSpace
