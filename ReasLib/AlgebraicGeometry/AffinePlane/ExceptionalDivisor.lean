/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Rees.Blowup
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree

/-!
# Exceptional divisor of the affine-plane blowup

The standard blowup of the affine plane at the origin, its exceptional fibre,
and the ideal sheaf and degree statements attached to that fibre.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.AffinePlaneBlowup

/-- The polynomial coordinate ring `k[x, y]` of the affine plane. -/
abbrev coordinateRing (k : Type u) [Field k] : Type u :=
  PuncturedAffineSpace.coordinateRing (Fin 2) k

/-- The affine plane `A²_k = Spec(k[x, y])`. -/
abbrev affinePlane (k : Type u) [Field k] : Scheme.{u} :=
  PuncturedAffineSpace.coordinateSpectrum (Fin 2) k

/-- The origin ideal `m = (x, y)` in `k[x, y]`. -/
abbrev originIdeal (k : Type u) [Field k] : Ideal (coordinateRing k) :=
  PuncturedAffineSpace.originIdeal (Fin 2) k

/-- The origin of `A²_k`, as the prime spectrum point cut out by `m`. -/
abbrev origin (k : Type u) [Field k] : affinePlane k :=
  PuncturedAffineSpace.coordinateOrigin (Fin 2) k

/-- The origin ideal is the span of the two coordinate functions `X 0` and `X 1`. -/
theorem originIdeal_eq_span (k : Type u) [Field k] :
    originIdeal k = Ideal.span {MvPolynomial.X (0 : Fin 2), MvPolynomial.X 1} := by
  let J : Ideal (coordinateRing k) :=
    Ideal.span {MvPolynomial.X (0 : Fin 2), MvPolynomial.X 1}
  have hX (i : Fin 2) : MvPolynomial.X i ∈ J := by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact Ideal.subset_span (by simp)
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact Ideal.subset_span (by simp)
  have hfactor : Ideal.Quotient.mk J =
      ((Ideal.Quotient.mk J).comp MvPolynomial.C).comp
        (PuncturedAffineSpace.evalAtOrigin (Fin 2) k) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change Ideal.Quotient.mk J (MvPolynomial.C r) =
        Ideal.Quotient.mk J (MvPolynomial.C
          (MvPolynomial.eval₂ (algebraMap k k) (fun _ : Fin 2 ↦ 0) (MvPolynomial.C r)))
      rw [MvPolynomial.eval₂_C]
      rfl
    · intro i
      change Ideal.Quotient.mk J (MvPolynomial.X i) =
        Ideal.Quotient.mk J (MvPolynomial.C
          (MvPolynomial.eval₂ (algebraMap k k) (fun _ : Fin 2 ↦ 0) (MvPolynomial.X i)))
      rw [MvPolynomial.eval₂_X, map_zero, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hX i)
  apply le_antisymm
  · intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hp' : PuncturedAffineSpace.evalAtOrigin (Fin 2) k p = 0 := hp
    calc
      Ideal.Quotient.mk J p = Ideal.Quotient.mk J
          (MvPolynomial.C (PuncturedAffineSpace.evalAtOrigin (Fin 2) k p)) :=
        RingHom.congr_fun hfactor p
      _ = 0 := by rw [hp', map_zero, map_zero]
  · refine Ideal.span_le.mpr ?_
    rintro p (rfl | rfl) <;> exact MvPolynomial.eval₂_X _ _ _

/-- The blowup `X = Proj(⨁ n, m^n)` of the affine plane in the origin. -/
abbrev scheme (k : Type u) [Field k] : Scheme.{u} :=
  Proj (ReesAlgebra.Grading.grade (originIdeal k))

/-- The blowup morphism `b : X ⟶ A²_k`. -/
abbrev hom (k : Type u) [Field k] : scheme k ⟶ affinePlane k :=
  ReesProj.toSpec (originIdeal k)

/-- The scheme-theoretic fibre `E` of `b` over the origin. -/
abbrev exceptionalFiber (k : Type u) [Field k] : Scheme.{u} :=
  (hom k).fiber (origin k)

/-- The closed immersion of the exceptional fibre into the blowup. -/
abbrev exceptionalι (k : Type u) [Field k] : exceptionalFiber k ⟶ scheme k :=
  (hom k).fiberι (origin k)

/-- The ideal sheaf `𝒪_X(-E)` of the exceptional fibre in the blowup. -/
abbrev negSheaf (k : Type u) [Field k] : (scheme k).Modules :=
  RingedSpace.Hom.idealSheaf (exceptionalι k).toShHom

/-- The restriction `𝒪_X(-E)|_E` of the ideal sheaf of the exceptional fibre. -/
abbrev restriction (k : Type u) [Field k] : (exceptionalFiber k).Modules :=
  (Scheme.Modules.pullback (exceptionalι k)).obj (negSheaf k)

/-- Constants in `k`, as elements of the residue field of the origin. -/
def originIdealResidueFieldFromBase (k : Type u) [Field k] :
    k →+* (origin k).asIdeal.ResidueField :=
  (algebraMap (coordinateRing k ⧸ (origin k).asIdeal)
      ((origin k).asIdeal.ResidueField)).comp
    ((Ideal.Quotient.mk (origin k).asIdeal).comp (algebraMap k (coordinateRing k)))

/-- The residue field of the origin ideal maps back to the polynomial base ring. -/
def originIdealResidueFieldToBase (k : Type u) [Field k] :
    (origin k).asIdeal.ResidueField →+* k :=
  IsFractionRing.lift
    (A := coordinateRing k ⧸ (origin k).asIdeal) (K := (origin k).asIdeal.ResidueField)
    (g := RingHom.kerLift (PuncturedAffineSpace.evalAtOrigin (Fin 2) k))
    (RingHom.kerLift_injective (PuncturedAffineSpace.evalAtOrigin (Fin 2) k))

/-- Sending a scalar into the residue field and then back to `k` is the identity on `k`. -/
theorem originIdealResidueFieldToBase_comp_fromBase (k : Type u) [Field k] :
    (originIdealResidueFieldToBase k).comp (originIdealResidueFieldFromBase k) =
      RingHom.id k := by
  apply RingHom.ext
  intro r
  change IsFractionRing.lift
      (A := coordinateRing k ⧸ (origin k).asIdeal) (K := (origin k).asIdeal.ResidueField)
      (g := RingHom.kerLift (PuncturedAffineSpace.evalAtOrigin (Fin 2) k))
      (RingHom.kerLift_injective (PuncturedAffineSpace.evalAtOrigin (Fin 2) k))
      (algebraMap (coordinateRing k ⧸ (origin k).asIdeal) ((origin k).asIdeal.ResidueField)
        (Ideal.Quotient.mk (origin k).asIdeal (algebraMap k (coordinateRing k) r))) = r
  rw [IsFractionRing.lift_algebraMap]
  change PuncturedAffineSpace.evalAtOriginAlgHom (Fin 2) k
    (algebraMap k (coordinateRing k) r) = r
  exact (PuncturedAffineSpace.evalAtOriginAlgHom (Fin 2) k).commutes r

/-- Sending a residue-field element to `k` and then back is the identity on the residue field. -/
theorem originIdealResidueFieldFromBase_comp_toBase (k : Type u) [Field k] :
    (originIdealResidueFieldFromBase k).comp (originIdealResidueFieldToBase k) =
      RingHom.id _ := by
  apply RingHom.ext
  intro r
  apply (originIdealResidueFieldToBase k).injective
  exact RingHom.congr_fun (originIdealResidueFieldToBase_comp_fromBase k)
    (originIdealResidueFieldToBase k r)

/-- The residue field of the origin ideal is canonically identified with `k`. -/
def originIdealResidueFieldEquiv (k : Type u) [Field k] :
    (origin k).asIdeal.ResidueField ≃+* k :=
  RingEquiv.ofRingHom (originIdealResidueFieldToBase k) (originIdealResidueFieldFromBase k)
    (originIdealResidueFieldToBase_comp_fromBase k) (originIdealResidueFieldFromBase_comp_toBase k)

/-- The residue field of the origin point of `A²_k` is canonically `k`. -/
def originResidueFieldIso (k : Type u) [Field k] :
    (affinePlane k).residueField (origin k) ≅ CommRingCat.of k :=
  (Scheme.Spec.residueFieldIso (.of (coordinateRing k)) (origin k)).trans
    (originIdealResidueFieldEquiv k).toCommRingCatIso

/-- The inverse of `originResidueFieldIso` is the constant-polynomial section. -/
theorem originResidueFieldIso_inv (k : Type u) [Field k] :
    (originResidueFieldIso k).inv =
      CommRingCat.ofHom (originIdealResidueFieldFromBase k) ≫
        (Scheme.Spec.residueFieldIso (.of (coordinateRing k)) (origin k)).inv := rfl

/-- The structure morphism of the exceptional fibre over `Spec k`. -/
abbrev exceptionalToSpec (k : Type u) [Field k] :
    exceptionalFiber k ⟶ Spec (CommRingCat.of k) :=
  (hom k).fiberToSpecResidueField (origin k) ≫ Spec.map (originResidueFieldIso k).inv

/-- The exceptional fibre is proper over `Spec k`. -/
instance exceptionalToSpec_isProper (k : Type u) [Field k] :
    IsProper (exceptionalToSpec k) := by
  let I := originIdeal k
  letI : Algebra (coordinateRing k) (ReesAlgebra.Grading.grade I 0) :=
    SetLike.GradeZero.instAlgebra (ReesAlgebra.Grading.grade I)
  letI : IsScalarTower (coordinateRing k) (ReesAlgebra.Grading.grade I 0) (reesAlgebra I) :=
    IsScalarTower.of_algebraMap_eq' (R := coordinateRing k)
      (S := ReesAlgebra.Grading.grade I 0) (A := reesAlgebra I) rfl
  letI : Algebra.FiniteType (ReesAlgebra.Grading.grade I 0) (reesAlgebra I) :=
    Algebra.FiniteType.of_restrictScalars_finiteType
      (coordinateRing k) (ReesAlgebra.Grading.grade I 0) (reesAlgebra I)
  letI : IsProper (ReesProj.degreeZeroSpecIso I).hom :=
    MorphismProperty.of_isIso @IsProper _
  letI : IsProper (hom k) := by
    unfold hom ReesProj.toSpec
    infer_instance
  letI : IsProper ((hom k).fiberToSpecResidueField (origin k)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  letI : IsProper (Spec.map (originResidueFieldIso k).inv) :=
    MorphismProperty.of_isIso @IsProper _
  unfold exceptionalToSpec
  infer_instance

/-- The exceptional fibre has topological Krull dimension at most one. -/
theorem exceptionalFiber_topologicalKrullDim_le_one (k : Type u) [Field k] :
    topologicalKrullDim (exceptionalFiber k) ≤ 1 := sorry

/-- The restriction `𝒪_X(-E)|_E` is an invertible sheaf on the exceptional fibre. -/
instance restriction_isInvertible (k : Type u) [Field k] :
    Scheme.Modules.Invertible (restriction k) := sorry

/-- The constant-polynomial section sends a scalar to the class of its constant polynomial. -/
theorem originIdealResidueFieldFromBase_apply (k : Type u) [Field k] (r : k) :
    originIdealResidueFieldFromBase k r =
      algebraMap (coordinateRing k ⧸ (origin k).asIdeal) ((origin k).asIdeal.ResidueField)
        (Ideal.Quotient.mk (origin k).asIdeal (algebraMap k (coordinateRing k) r)) := rfl

/-- The exceptional fibre is isomorphic over `Spec k` to the projective line. -/
theorem exceptionalFiber_isIsomorphic_projectiveLine (k : Type u) [Field k] :
    IsIsomorphic (Over.mk (exceptionalToSpec k)) (ProjectiveSpace.schemeOver k 1) := sorry

/-- The exceptional fibre immersion is an effective Cartier divisor. -/
instance exceptionalι_isEffectiveCartierDivisor (k : Type u) [Field k] :
    IsEffectiveCartierDivisor (exceptionalι k) := sorry

/-- The restricted ideal sheaf has degree one on the exceptional fibre. -/
theorem restriction_curveDegree_eq_one (k : Type u) [Field k] :
    Scheme.Modules.curveDegreeOfInvertible (exceptionalToSpec k)
      (exceptionalFiber_topologicalKrullDim_le_one k) (restriction k) = 1 := sorry

end AlgebraicGeometry.AffinePlaneBlowup
