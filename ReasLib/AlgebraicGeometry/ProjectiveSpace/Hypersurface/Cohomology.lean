/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hypersurface
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.CanonicalAlgebra
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.TwistCohomology.Naturality
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Delta
public import ReasLib.AlgebraicGeometry.Scheme.Module.ClosedImmersion.Exact
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal

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
      (SheafOfModules.unit (ProjectiveSpace.scheme A n).ringCatSheaf) := by
  exact ⟨(asIso (Proj.AssociatedModule.CanonicalAlgebra.unitHom
    (ProjectiveSpace.grading A n))).symm⟩

/-- The third term of `sequence n d F hF` is isomorphic to `i_* O_X`. -/
theorem pushforward_pullback_zero_isIsomorphic_pushforwardStructure
    {A : Type u} [CommRing A] (n d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) A) (hF : F ∈ ProjectiveSpace.grading A n d) :
    IsIsomorphic
      ((Scheme.Modules.pushforward (closedImmersion n d F hF)).obj
        ((Scheme.Modules.pullback (closedImmersion n d F hF)).obj
          (twistingSheaf A n 0)))
      (pushforwardStructure n d F hF) := by
  obtain ⟨e⟩ := twistingSheaf_zero_isIsomorphic_unit (A := A) n
  exact ⟨(Scheme.Modules.pushforward (closedImmersion n d F hF)).mapIso
    ((Scheme.Modules.pullback (closedImmersion n d F hF)).mapIso e ≪≫
      (Scheme.Modules.pullback (closedImmersion n d F hF)).mapIso
        (RingedSpace.unitIsoTensorUnit (ProjectiveSpace.scheme A n).toRingedSpace) ≪≫
      Scheme.Modules.pullbackUnitIso (closedImmersion n d F hF) ≪≫
      (RingedSpace.unitIsoTensorUnit (scheme n d F hF).toRingedSpace).symm)⟩

/-- If `F` is a nonzerodivisor, the multiplication-restriction complex of `V₊(F)` is short
exact. -/
theorem sequence_shortExact {A : Type u} [CommRing A] (n d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) A) (hF : F ∈ ProjectiveSpace.grading A n d)
    (hF_nzd : F ∈ nonZeroDivisors (MvPolynomial (Fin (n + 1)) A)) :
    (sequence n d F hF).ShortExact := sorry

variable {A : Type u} [CommRing A] (n d : ℕ)
variable (F : MvPolynomial (Fin (n + 1)) A) (hF : F ∈ ProjectiveSpace.grading A n d)

private theorem cohomology_delta_isZero_iff {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (M : X.Modules) (q : ℕ) :
    IsZero ((((RingedSpace.Module.Derived.GlobalSections.Delta.cohomology
      X.toRingedSpace).F q).obj).obj M) ↔
      IsZero (Scheme.Hom.cohomology f M q) := by
  rw [RingedSpace.Module.Derived.GlobalSections.Delta.degree_obj_eq_moduleCohomologyAtOpen]
  change IsZero (Scheme.Modules.cohomology M q) ↔
    IsZero ((ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap f)).obj
      (Scheme.Modules.cohomology M q))
  constructor
  · exact (ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap f)).map_isZero
  · intro h
    rw [IsZero.iff_id_eq_zero]
    apply (ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap f)).map_injective
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
    exact h.eq_zero_of_src _

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
        (SheafOfModules.unit (scheme n d F hF).ringCatSheaf) q) := by
  let H := RingedSpace.Module.Derived.GlobalSections.Delta.cohomology
    (ProjectiveSpace.scheme A n).toRingedSpace
  have hvan (r : ℕ) (hr0 : r ≠ 0) (hrn : r ≠ n) (k : ℤ) :
      IsZero (((H.F r).obj).obj (twistingSheaf A n k)) := by
    exact (cohomology_delta_isZero_iff (ProjectiveSpace.toSpec A n) _ r).mpr
      (twistingSheaf.cohomology_isZero_of_ne A n hn k r hr0 hrn)
  have hthird := ((H.exact₅
    (sequence_shortExact n d F hF hF_nzd) q).exact 1).isZero_of_both_isZero
      (hvan q (by omega) (by omega) 0)
      (hvan (q + 1) (by omega) (by omega) (-d))
  have hzero := (cohomology_delta_isZero_iff (ProjectiveSpace.toSpec A n)
    (sequence n d F hF).X₃ q).mp hthird
  obtain ⟨e⟩ := pushforward_pullback_zero_isIsomorphic_pushforwardStructure n d F hF
  obtain ⟨e'⟩ := cohomology_iso_pushforward n d F hF q
  exact (hzero.of_iso ((Scheme.Hom.cohomologyFunctor
    (ProjectiveSpace.toSpec A n) q).mapIso e).symm).of_iso e'

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
        (twistingSheaf A n (-d)) n) := by
  let H := RingedSpace.Module.Derived.GlobalSections.Delta.cohomology
    (ProjectiveSpace.scheme A n).toRingedSpace
  let hS := sequence_shortExact n d F hF hF_nzd
  have hzero (r : ℕ) (hr : 0 < r) :
      IsZero (((H.F r).obj).obj (twistingSheaf A n 0)) := by
    exact (cohomology_delta_isZero_iff (ProjectiveSpace.toSpec A n) _ r).mpr
      (twistingSheaf.cohomology_isZero_of_not_cases A n r 0 (by omega) (by omega))
  haveI : Mono (H.δ hS (n - 1)) :=
    ((H.exact₅ hS (n - 1)).exact 1).mono_g
      ((hzero (n - 1) (by omega)).eq_zero_of_src _)
  haveI : Epi (H.δ hS (n - 1)) :=
    ((H.exact₅ hS (n - 1)).exact 2).epi_f
      ((hzero (n - 1 + 1) (by omega)).eq_zero_of_tgt _)
  have hn1 : n - 1 + 1 = n := by omega
  haveI : IsIso (H.δ hS (n - 1)) := isIso_of_mono_of_epi _
  have eδ := asIso (H.δ hS (n - 1))
  rw [hn1] at eδ
  let e := (eqToIso
    (RingedSpace.Module.Derived.GlobalSections.Delta.degree_obj_eq_moduleCohomologyAtOpen
      (ProjectiveSpace.scheme A n).toRingedSpace (sequence n d F hF).X₃ (n - 1))).symm ≪≫
    eδ ≪≫ eqToIso
      (RingedSpace.Module.Derived.GlobalSections.Delta.degree_obj_eq_moduleCohomologyAtOpen
        (ProjectiveSpace.scheme A n).toRingedSpace (twistingSheaf A n (-d)) n)
  obtain ⟨e₁⟩ := cohomology_iso_pushforward n d F hF (n - 1)
  obtain ⟨e₂⟩ := pushforward_pullback_zero_isIsomorphic_pushforwardStructure n d F hF
  exact ⟨e₁ ≪≫ (Scheme.Hom.cohomologyFunctor
    (ProjectiveSpace.toSpec A n) (n - 1)).mapIso e₂.symm ≪≫
      (ModuleCat.restrictScalars
        (Scheme.Hom.globalSectionsMap (ProjectiveSpace.toSpec A n))).mapIso e⟩

end AlgebraicGeometry.ProjectiveSpace.Hypersurface
