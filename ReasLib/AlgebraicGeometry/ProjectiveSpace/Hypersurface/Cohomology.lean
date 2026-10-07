module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hypersurface
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.TwistCohomology.Naturality
public import ReasLib.AlgebraicGeometry.Scheme.Module.ClosedImmersion.Exact
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections

/-!
# Structure-sheaf cohomology of projective hypersurfaces

The multiplication-restriction complex, pushforward comparison, and vanishing in degrees
`q` with `0 < q` and `n ≤ q` hold for every homogeneous form. Short exactness,
intermediate-degree vanishing, and the cokernel and top-degree identifications require
the form to be a nonzerodivisor.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.Hypersurface

/-- Multiplication by the degree-`d` form `F`, as a map `O_{P^n}(-d) ⟶ O_{P^n}(0)`. -/
def multiplication {A : Type u} [CommRing A] (n d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) A) (hF : F ∈ ProjectiveSpace.grading A n d) :
    twistingSheaf A n (-d) ⟶ twistingSheaf A n 0 :=
  twistingSheaf.mulHomogeneous n (-d) d F hF ≫
    eqToHom (congrArg (twistingSheaf A n) (neg_add_cancel (d : ℤ)))

/-- The adjunction unit `O_{P^n}(0) ⟶ i_* i^* O_{P^n}(0)` along `closedImmersion n d F hF`. -/
def restriction {A : Type u} [CommRing A] (n d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) A) (hF : F ∈ ProjectiveSpace.grading A n d) :
    twistingSheaf A n 0 ⟶
      (Scheme.Modules.pushforward (closedImmersion n d F hF)).obj
        ((Scheme.Modules.pullback (closedImmersion n d F hF)).obj
          (twistingSheaf A n 0)) :=
  Scheme.Modules.ClosedImmersion.restrictionMap
    (closedImmersion n d F hF) (twistingSheaf A n 0)

/-- Multiplication by `F` followed by restriction to the hypersurface is the zero map. -/
theorem multiplication_comp_restriction {A : Type u} [CommRing A] (n d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) A) (hF : F ∈ ProjectiveSpace.grading A n d) :
    multiplication n d F hF ≫ restriction n d F hF = 0 := sorry

/-- The three-term complex `O_{P^n}(-d) ⟶ O_{P^n}(0) ⟶ i_* i^* O_{P^n}(0)` associated to
`V₊(F)`. -/
def sequence {A : Type u} [CommRing A] (n d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) A) (hF : F ∈ ProjectiveSpace.grading A n d) :
    ShortComplex (ProjectiveSpace.scheme A n).Modules :=
  ShortComplex.mk (multiplication n d F hF) (restriction n d F hF)
    (multiplication_comp_restriction n d F hF)

/-- The pushforward `i_* O_X` of the structure sheaf of the hypersurface. -/
def pushforwardStructure {A : Type u} [CommRing A] (n d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) A) (hF : F ∈ ProjectiveSpace.grading A n d) :
    (ProjectiveSpace.scheme A n).Modules :=
  (Scheme.Modules.pushforward (closedImmersion n d F hF)).obj
    (SheafOfModules.unit (scheme n d F hF).ringCatSheaf)

/-- The degree-zero twisting sheaf on `P^n_A` is isomorphic to the structure sheaf. -/
theorem twistingSheaf_zero_isIsomorphic_unit {A : Type u} [CommRing A] (n : ℕ) :
    IsIsomorphic (twistingSheaf A n 0)
      (SheafOfModules.unit (ProjectiveSpace.scheme A n).ringCatSheaf) := sorry

/-- The third term of `sequence n d F hF` is isomorphic to `i_* O_X`. -/
theorem pushforward_pullback_zero_isIsomorphic_pushforwardStructure
    {A : Type u} [CommRing A] (n d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) A) (hF : F ∈ ProjectiveSpace.grading A n d) :
    IsIsomorphic
      ((Scheme.Modules.pushforward (closedImmersion n d F hF)).obj
        ((Scheme.Modules.pullback (closedImmersion n d F hF)).obj
          (twistingSheaf A n 0)))
      (pushforwardStructure n d F hF) := sorry

/-- If `F` is a nonzerodivisor, the multiplication-restriction complex of `V₊(F)` is short
exact. -/
theorem sequence_shortExact {A : Type u} [CommRing A] (n d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) A) (hF : F ∈ ProjectiveSpace.grading A n d)
    (hF_nzd : F ∈ nonZeroDivisors (MvPolynomial (Fin (n + 1)) A)) :
    (sequence n d F hF).ShortExact := sorry

variable {A : Type u} [CommRing A] (n d : ℕ)
variable (F : MvPolynomial (Fin (n + 1)) A) (hF : F ∈ ProjectiveSpace.grading A n d)

/-- Cohomology of `O_X` along `X ⟶ Spec A` agrees with cohomology of `i_* O_X` along
`P^n_A ⟶ Spec A`. -/
theorem cohomology_iso_pushforward (q : ℕ) :
    IsIsomorphic
      (Scheme.Hom.cohomology (hom n d F hF)
        (SheafOfModules.unit (scheme n d F hF).ringCatSheaf) q)
      (Scheme.Hom.cohomology (ProjectiveSpace.toSpec A n)
        (pushforwardStructure n d F hF) q) := sorry

/-- For a homogeneous nonzerodivisor `F` on `P^n_A` with `0 < n`, the structure-sheaf
cohomology of `V₊(F)` vanishes in degrees `q` satisfying `0 < q` and `q + 1 < n`. -/
theorem cohomology_isZero_of_lt (hn : 0 < n)
    (hF_nzd : F ∈ nonZeroDivisors (MvPolynomial (Fin (n + 1)) A))
    (q : ℕ) (hq0 : 0 < q) (hqn : q + 1 < n) :
    IsZero
      (Scheme.Hom.cohomology (hom n d F hF)
        (SheafOfModules.unit (scheme n d F hF).ringCatSheaf) q) := sorry

/-- For every homogeneous form `F` on `P^n_A`, the structure-sheaf cohomology of
`V₊(F)` vanishes in degrees `q` satisfying `0 < q` and `n ≤ q`. -/
theorem cohomology_isZero_of_ge (q : ℕ) (hq0 : 0 < q) (hqn : n ≤ q) :
    IsZero
      (Scheme.Hom.cohomology (hom n d F hF)
        (SheafOfModules.unit (scheme n d F hF).ringCatSheaf) q) := sorry

/-- For a homogeneous nonzerodivisor `F` on `P^n_A` with `2 ≤ n`, degree-zero cohomology
of `O_{V₊(F)}` is isomorphic to the cokernel of multiplication by `F` on ambient degree-zero
twist cohomology. -/
theorem cohomology_zero_isCokernel (hn : 2 ≤ n)
    (hF_nzd : F ∈ nonZeroDivisors (MvPolynomial (Fin (n + 1)) A)) :
    IsIsomorphic
      (Scheme.Hom.cohomology (hom n d F hF)
        (SheafOfModules.unit (scheme n d F hF).ringCatSheaf) 0)
      (cokernel
        ((Scheme.Hom.cohomologyFunctor (ProjectiveSpace.toSpec A n) 0).map
          (multiplication n d F hF))) := sorry

/-- For a homogeneous nonzerodivisor `F` of degree `d` on `P^n_A` with `2 ≤ n`,
`H^{n-1}(V₊(F), O_{V₊(F)})` is isomorphic to `H^n(P^n_A, O(-d))`. -/
theorem cohomology_pred_isTop (hn : 2 ≤ n)
    (hF_nzd : F ∈ nonZeroDivisors (MvPolynomial (Fin (n + 1)) A)) :
    IsIsomorphic
      (Scheme.Hom.cohomology (hom n d F hF)
        (SheafOfModules.unit (scheme n d F hF).ringCatSheaf) (n - 1))
      (Scheme.Hom.cohomology (ProjectiveSpace.toSpec A n)
        (twistingSheaf A n (-d)) n) := sorry

end AlgebraicGeometry.ProjectiveSpace.Hypersurface
