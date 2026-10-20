/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.PlaneCurve.Cohomology

/-!
# Plane-curve construction compatibility

Transparent dimension-two specializations retain the plane-curve construction API.
The quotient, closed immersion, and multiplication–restriction complex are supplied
by the canonical projective-hypersurface owners.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.PlaneCurve

variable {k : Type u} [Field k] (d : ℕ) (F : MvPolynomial (Fin 3) k)
  (hF : F ∈ ProjectiveSpace.grading k 2 d)

/-- The homogeneous principal ideal of a plane equation. -/
abbrev homogeneousIdeal := Hypersurface.homogeneousIdeal 2 d F hF

/-- The canonical quotient grading for a plane equation. -/
abbrev quotientGrading := Hypersurface.quotientGrading 2 d F hF

/-- The projective hypersurface of a plane equation. -/
abbrev scheme := Hypersurface.scheme 2 d F hF

/-- The canonical closed immersion of a plane hypersurface. -/
abbrev closedImmersion := Hypersurface.closedImmersion 2 d F hF

/-- The canonical structure morphism of a plane hypersurface. -/
abbrev hom := Hypersurface.hom 2 d F hF

#check (Hypersurface.homogeneousIdeal_toIdeal 2 d F hF :
  (homogeneousIdeal d F hF).toIdeal = Ideal.span {F})

#check (Hypersurface.sequence 2 d F hF :
  ShortComplex (ProjectiveSpace.scheme k 2).Modules)

#check (Hypersurface.twistingSheaf_zero_isIsomorphic_unit (A := k) 2 :
  IsIsomorphic (twistingSheaf k 2 0)
    (SheafOfModules.unit (ProjectiveSpace.scheme k 2).ringCatSheaf))

#check (Hypersurface.pushforward_pullback_zero_isIsomorphic_pushforwardStructure 2 d F hF :
  IsIsomorphic
    ((Scheme.Modules.pushforward (closedImmersion d F hF)).obj
      ((Scheme.Modules.pullback (closedImmersion d F hF)).obj (twistingSheaf k 2 0)))
    (Hypersurface.pushforwardStructure 2 d F hF))

#check (inferInstance : IsProper (hom d F hF))

#check (inferInstance : (twistingSheaf k 2 (-d)).IsCoherent)

end AlgebraicGeometry.ProjectiveSpace.PlaneCurve
