/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hypersurface
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

/-!
# Adjunction for smooth plane curves

The relative differential sheaf of a smooth degree-`d` plane curve is the
restriction of the projective twisting sheaf of integer degree `d - 3`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.PlaneCurve

variable {k : Type u} [Field k] (d : ℕ) (F : MvPolynomial (Fin 3) k)
  (hF : F ∈ ProjectiveSpace.grading k 2 d)

/-- The relative differential sheaf of a smooth degree-`d` plane curve is isomorphic
to the restriction of `O(d - 3)` from projective space. -/
theorem canonicalSheaf_isIsomorphic
    [Curve (Over.mk (Hypersurface.hom 2 d F hF))]
    [Smooth (Hypersurface.hom 2 d F hF)] :
    IsIsomorphic
      ((Scheme.Modules.pullback (Hypersurface.closedImmersion 2 d F hF)).obj
        (twistingSheaf k 2 ((d : ℤ) - 3)))
      Ω[(Hypersurface.hom 2 d F hF).toShHom] := sorry

end AlgebraicGeometry.ProjectiveSpace.PlaneCurve
