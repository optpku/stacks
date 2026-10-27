/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.Fiber

/-!
# Compactifications of geometric fibres
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Compactification

open AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (ybar : GeometricPoint Y)
variable (P : Of Y (Over.mk f))

/-- Compactification of the geometric fibre `X_ȳ ⟶ Spec k` obtained by
base-changing a compactification of `f` along `ȳ`. -/
abbrev geometricFiber :
    Of (Spec (CommRingCat.of ybar.K)) (Over.mk (Hom.geometricFiberToPoint f ybar)) :=
  compactificationPullback f ybar.hom (geometricFiberToPoint f ybar)
    (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P

/-- The fibre compactification is the cartesian pullback of `P` along `ȳ`. -/
theorem geometricFiber_eq :
    geometricFiber f ybar P =
      compactificationPullback f ybar.hom (geometricFiberToPoint f ybar)
        (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P :=
  sorry

/-- The interior immersion of the fibre compactification is the induced lift
`j'`. -/
theorem geometricFiber_ι :
    Of.ι (geometricFiber f ybar P) =
      interiorLift f ybar.hom (geometricFiberToPoint f ybar)
        (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P :=
  sorry

/-- The structure map of the fibre compactification is the ambient projection
`f̄'`. -/
theorem geometricFiber_hom :
    (geometricFiber f ybar P).obj.right.hom =
      ambientToBase f ybar.hom (geometricFiberToPoint f ybar)
        (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P :=
  sorry

end AlgebraicGeometry.Scheme.Compactification

end
