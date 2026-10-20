module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FittingIdeal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealStalk

/-!
# Stalks of Fitting ideal sheaves on algebraic spaces

The stalk of a Fitting ideal sheaf is the image ideal of its inclusion in the
structure sheaf, viewed in the étale local ring.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped FittingIdeal

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The stalk of `fittingIdealSheaf F r` at a geometric point `xbar`, as an ideal of
the étale local ring `𝒪_{X, x̄}`. -/
def fittingIdealStalkIdeal {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (r : ℕ) (xbar : GeometricPoint X) :
    Ideal (etaleLocalRing X xbar) :=
  Modules.stalkImageIdeal xbar (fittingIdealSheaf F r).arrow

/-- For a finite-type quasi-coherent module, the stalk of the Fitting ideal sheaf
agrees with the intrinsic Fitting ideal of the étale module stalk. -/
theorem fittingIdealStalkIdeal_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ)
    (xbar : GeometricPoint X) :
    fittingIdealStalkIdeal F r xbar =
      Fit[etaleLocalRing X xbar]_(r)(Modules.stalkModuleCat xbar F) :=
  sorry

/-- An element of `𝒪_{X, x̄}` lies in `fittingIdealStalkIdeal F r xbar` exactly when it
is the image of an element of the étale stalk of `fittingIdealSheaf F r`. -/
theorem mem_fittingIdealStalkIdeal_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (r : ℕ) (xbar : GeometricPoint X)
    (a : etaleLocalRing X xbar) :
    a ∈ fittingIdealStalkIdeal F r xbar ↔
      ∃ s : Modules.stalkModuleCat xbar (fittingIdealSheaf F r : X.Modules),
        Modules.stalkToRing xbar (fittingIdealSheaf F r).arrow s = a :=
  Iff.rfl

end AlgebraicGeometry.AlgebraicSpace
