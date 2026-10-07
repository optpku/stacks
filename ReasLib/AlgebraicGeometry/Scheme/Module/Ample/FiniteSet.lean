module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample

/-!
# Affine nonvanishing neighborhoods of finite sets

An ample invertible module supplies affine nonvanishing opens containing a prescribed finite
set and contained in a prescribed ambient open.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsAmple

/-- For an ample invertible module, a finite set contained in an open is contained in an affine
nonvanishing open of a positive tensor-power section that is itself contained in that open. -/
theorem exists_affineNonvanishingOpen_between
    {X : Scheme.{u}} {L : X.Modules} [hL : Invertible L]
    (hA : IsAmple L) (E : Set X) (hE : E.Finite)
    (W : X.Opens) (hEW : E ⊆ (W : Set X)) :
    ∃ n : ℕ+,
      ∃ s : Γ(RingedSpace.TensorPower.sheaf L n, ⊤),
        IsAffineOpen (hL.nonvanishingOpen s) ∧
          E ⊆ (hL.nonvanishingOpen s : Set X) ∧ hL.nonvanishingOpen s ≤ W := sorry

end AlgebraicGeometry.Scheme.Modules.IsAmple
