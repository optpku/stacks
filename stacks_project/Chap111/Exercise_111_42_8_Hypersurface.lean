module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hypersurface
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hypersurface.Cohomology

/-!
# Hypersurface construction and multiplication-restriction sequence

Typed checks expose the canonical mathematical owners to existing importers.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace (twistingSheaf)
open AlgebraicGeometry.ProjectiveSpace.Hypersurface

universe u

section

variable {A : Type u} [CommRing A] (n d : ℕ)
variable (F : MvPolynomial (Fin (n + 1)) A) (hF : F ∈ ProjectiveSpace.grading A n d)

#check
  (GradedAlgebra.Quotient.spanSingleton_isHomogeneous (ProjectiveSpace.grading A n) ⟨d, hF⟩ :
    (Ideal.span {F}).IsHomogeneous (ProjectiveSpace.grading A n))

#check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.homogeneousIdeal n d F hF :
    HomogeneousIdeal (ProjectiveSpace.grading A n))

#check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.homogeneousIdeal_toIdeal n d F hF :
    (homogeneousIdeal n d F hF).toIdeal = Ideal.span {F})

#check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.quotientGrading n d F hF :
    ℕ → Submodule A (MvPolynomial (Fin (n + 1)) A ⧸ (homogeneousIdeal n d F hF).toIdeal))

#check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.instGradedAlgebra n d F hF :
    GradedAlgebra (quotientGrading n d F hF))

#check (AlgebraicGeometry.ProjectiveSpace.Hypersurface.scheme n d F hF : Scheme)

#check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.closedImmersion n d F hF :
    scheme n d F hF ⟶ ProjectiveSpace.scheme A n)

#check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.instIsClosedImmersion n d F hF :
    IsClosedImmersion (closedImmersion n d F hF))

#check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.hom n d F hF :
    scheme n d F hF ⟶ Spec (.of A))

#check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.multiplication n d F hF :
    twistingSheaf A n (-d) ⟶ twistingSheaf A n 0)

#check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.restriction n d F hF :
    twistingSheaf A n 0 ⟶
      (Scheme.Modules.pushforward (closedImmersion n d F hF)).obj
        ((Scheme.Modules.pullback (closedImmersion n d F hF)).obj (twistingSheaf A n 0)))

#check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.multiplication_comp_restriction n d F hF :
    multiplication n d F hF ≫ restriction n d F hF = 0)

#check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.sequence n d F hF :
    ShortComplex (ProjectiveSpace.scheme A n).Modules)

#check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.pushforwardStructure n d F hF :
    (ProjectiveSpace.scheme A n).Modules)

#check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.twistingSheaf_zero_isIsomorphic_unit
      (A := A) n :
    IsIsomorphic (twistingSheaf A n 0)
      (SheafOfModules.unit (ProjectiveSpace.scheme A n).ringCatSheaf))

#check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.pushforward_pullback_zero_isIsomorphic_pushforwardStructure
      n d F hF :
    IsIsomorphic
      ((Scheme.Modules.pushforward (closedImmersion n d F hF)).obj
        ((Scheme.Modules.pullback (closedImmersion n d F hF)).obj (twistingSheaf A n 0)))
      (pushforwardStructure n d F hF))

#check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.sequence_shortExact n d F hF :
    ∀ (hF_nzd : F ∈ nonZeroDivisors (MvPolynomial (Fin (n + 1)) A)),
    (sequence n d F hF).ShortExact)

end
