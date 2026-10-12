/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Blowup.AffineChart
import StacksCheckRecall

open scoped nonZeroDivisors

universe u

/- Lemma 31.32.6: for a chosen blowup `π` of `X` along `I`, an affine open `U`, an
element `a : I.ideal U`, and a point `x'` over `U`, the point lies in the canonical affine
chart associated to `a` if and only if the image of `a` in the stalk at `x'` is a
nonzerodivisor generating the stalk ideal of the exceptional divisor. -/
@[stacks 0BFL] #check
  (AlgebraicGeometry.Blowup.mem_affineChartOpen_iff_exceptionalDivisor_stalkIdeal_eq_span :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} {I : X.IdealSheafData}
      (π : AlgebraicGeometry.Blowup X I) (U : X.affineOpens) (a : I.ideal U)
      (x' : π.scheme) (hxU : π.hom x' ∈ (U : Set X)),
      x' ∈ π.affineChartOpen U a ↔
        let a_x' : π.scheme.presheaf.stalk x' :=
          (AlgebraicGeometry.Scheme.Hom.stalkMap π.hom x').hom
            (X.presheaf.germ (U : X.Opens) (π.hom x') hxU a.1)
        a_x' ∈ nonZeroDivisors (π.scheme.presheaf.stalk x') ∧
          AlgebraicGeometry.RingedSpace.idealSheafStalkIdeal
              π.exceptionalDivisor.toSubobject x' =
            Ideal.span ({a_x'} : Set (π.scheme.presheaf.stalk x')))
