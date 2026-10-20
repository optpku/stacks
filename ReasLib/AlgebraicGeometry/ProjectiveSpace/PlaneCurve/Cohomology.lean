/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hypersurface.Cohomology
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Proper
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist.Invertible
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

/-!
# Structure-sheaf cohomology of smooth plane curves

The canonical multiplication–restriction complex is short exact for a smooth plane
curve. Its global functions and first structure-sheaf cohomology give the ground
field and the degree–genus formula.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.PlaneCurve

/-- The third term `i_* i^* O_{P^2}(0)` of `Hypersurface.sequence 2 d F hF` is coherent. -/
instance instIsCoherent_pushforwardPullbackTwistingZero {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d) :
    ((Scheme.Modules.pushforward (Hypersurface.closedImmersion 2 d F hF)).obj
      ((Scheme.Modules.pullback (Hypersurface.closedImmersion 2 d F hF)).obj
        (twistingSheaf k 2 0))).IsCoherent := sorry

/-- The pushforward `i_* O_C` is coherent. -/
instance instIsCoherent_pushforwardStructure {k : Type u} [Field k] (d : ℕ)
    (F : MvPolynomial (Fin 3) k) (hF : F ∈ ProjectiveSpace.grading k 2 d) :
    (Hypersurface.pushforwardStructure 2 d F hF).IsCoherent := sorry

variable {k : Type u} [Field k] (d : ℕ) (F : MvPolynomial (Fin 3) k)
  (hF : F ∈ ProjectiveSpace.grading k 2 d)

/-- The multiplication–restriction complex of a smooth plane curve is short exact. -/
theorem structureSheafSequence_shortExact
    [Curve (Over.mk (Hypersurface.hom 2 d F hF))]
    [Smooth (Hypersurface.hom 2 d F hF)] :
    (Hypersurface.sequence 2 d F hF).ShortExact := sorry

/-- The canonical map from the ground field to the global functions of a smooth plane curve
is bijective. -/
theorem globalSectionsMap_bijective
    [Curve (Over.mk (Hypersurface.hom 2 d F hF))]
    [Smooth (Hypersurface.hom 2 d F hF)] :
    Function.Bijective (Scheme.Hom.globalSectionsMap (Hypersurface.hom 2 d F hF)) := sorry

/-- The dimension of the first structure-sheaf cohomology of a smooth degree-`d` plane
curve is `((d - 1) * (d - 2)) / 2`. -/
theorem genus_eq
    [Curve (Over.mk (Hypersurface.hom 2 d F hF))]
    [Smooth (Hypersurface.hom 2 d F hF)] :
    Scheme.Hom.cohomologyFinrank (Hypersurface.hom 2 d F hF)
        (SheafOfModules.unit (Hypersurface.scheme 2 d F hF).ringCatSheaf) 1 =
      ((d - 1) * (d - 2)) / 2 := sorry

end AlgebraicGeometry.ProjectiveSpace.PlaneCurve
