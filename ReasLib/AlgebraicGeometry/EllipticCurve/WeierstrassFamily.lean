/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
public import ReasLib.RingTheory.GradedAlgebra.Quotient
public import ReasLib.AlgebraicGeometry.EllipticCurve.Moduli

/-!
# The Weierstrass scheme

The affine scheme W = Spec of the localized Weierstrass ring, carrying the universal cubic,
its projection, and the infinity section (0 : 1 : 0).
-/

public section

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousIdeal HomogeneousLocalization
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.WeierstrassScheme

/-- The five Weierstrass coefficient indices a1, a2, a3, a4, a6. -/
inductive Coeff : Type
  /-- The coefficient a1. -/
  | a1
  /-- The coefficient a2. -/
  | a2
  /-- The coefficient a3. -/
  | a3
  /-- The coefficient a4. -/
  | a4
  /-- The coefficient a6. -/
  | a6
  deriving DecidableEq

/-- The polynomial ring ℤ[a1, a2, a3, a4, a6] in universe u. -/
abbrev coeffRing : Type u :=
  MvPolynomial (ULift.{u} Coeff) (ULift.{u} ℤ)

/-- The universal Weierstrass curve over ℤ[a1, a2, a3, a4, a6]. -/
@[expose]
def universal : WeierstrassCurve coeffRing where
  a₁ := MvPolynomial.X ⟨.a1⟩
  a₂ := MvPolynomial.X ⟨.a2⟩
  a₃ := MvPolynomial.X ⟨.a3⟩
  a₄ := MvPolynomial.X ⟨.a4⟩
  a₆ := MvPolynomial.X ⟨.a6⟩

/-- The discriminant Δ of the universal Weierstrass curve. -/
@[expose]
def Δ : coeffRing :=
  universal.Δ

/-- The coordinate ring of the Weierstrass scheme, obtained by inverting Δ. -/
abbrev ring : Type u :=
  Localization.Away Δ

/-- The Weierstrass curve with coefficients in the localized ring. -/
@[expose]
def curve : WeierstrassCurve ring :=
  universal.map (algebraMap coeffRing ring)

/-- The homogeneous Weierstrass cubic on P2 over the localized ring. -/
@[expose]
def projectivePolynomial : MvPolynomial (Fin 3) ring :=
  WeierstrassCurve.Projective.polynomial curve

/-- The homogeneous ideal of the universal Weierstrass cubic. -/
@[expose]
def projectiveIdeal : HomogeneousIdeal (ProjectiveSpace.grading ring 2) :=
  Ideal.homogeneousHull _ (Ideal.span {projectivePolynomial})

/-- The canonical graded-algebra structure on the homogeneous quotient by the Weierstrass cubic. -/
instance projectiveQuotientGradedAlgebra :
    GradedAlgebra
      (GradedAlgebra.Quotient.grading (ProjectiveSpace.grading ring 2)
        projectiveIdeal.toIdeal) :=
  GradedAlgebra.Quotient.gradedAlgebra _ _ projectiveIdeal.isHomogeneous

/-- The internal grading on the homogeneous quotient by the Weierstrass cubic. -/
abbrev familyGrading : ℕ → Submodule ring (MvPolynomial (Fin 3) ring ⧸ projectiveIdeal.toIdeal) :=
  GradedAlgebra.Quotient.grading (ProjectiveSpace.grading ring 2) projectiveIdeal.toIdeal

/-- The Weierstrass scheme W as Spec of the localized coefficient ring. -/
@[expose]
def scheme : Scheme.{u} :=
  Spec (.of ring)

/-- The structure morphism W to Spec ℤ. -/
@[expose]
def toSpecInt : scheme ⟶ EllipticCurve.Moduli.specInt :=
  Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) ring))

/-- The Weierstrass scheme as an object of the slice over Spec ℤ. -/
@[expose]
def overInt : Over EllipticCurve.Moduli.specInt :=
  Over.mk toSpecInt

/-- The total space E_W of the universal Weierstrass family, realized as the projective spectrum
of the homogeneous quotient by the Weierstrass cubic. -/
@[expose]
def familyTotal : Scheme.{u} :=
  Proj familyGrading

-- Canonical instance search for the localized quotient exceeds the default budget.
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
/-- The constant map into the degree-zero quotient preserves one, multiplication, zero,
and addition. -/
private theorem ringToDegreeZero_laws :
    let f : ring → familyGrading 0 := fun r ↦
      GradedAlgebra.Quotient.componentMap (ProjectiveSpace.grading ring 2)
        projectiveIdeal.toIdeal 0 (ProjectiveSpace.degreeZeroC ring 2 r)
    f 1 = 1 ∧ (∀ a b, f (a * b) = f a * f b) ∧
      f 0 = 0 ∧ (∀ a b, f (a + b) = f a + f b) := sorry

-- Canonical instance search for the localized quotient exceeds the default budget.
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
/-- Constants as a ring homomorphism into the degree-zero piece of the Weierstrass quotient. -/
private def ringToDegreeZero : ring →+* familyGrading 0 where
  toFun r :=
    GradedAlgebra.Quotient.componentMap (ProjectiveSpace.grading ring 2)
      projectiveIdeal.toIdeal 0 (ProjectiveSpace.degreeZeroC ring 2 r)
  map_one' := ringToDegreeZero_laws.1
  map_mul' := ringToDegreeZero_laws.2.1
  map_zero' := ringToDegreeZero_laws.2.2.1
  map_add' := ringToDegreeZero_laws.2.2.2

-- Canonical instance search for the localized quotient exceeds the default budget.
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
/-- The projection f_W : E_W to W, as the structure morphism of Proj of the Weierstrass
quotient. -/
def familyHom : familyTotal.{u} ⟶ scheme.{u} :=
  Proj.toSpecZero familyGrading ≫ Spec.map (CommRingCat.ofHom ringToDegreeZero)

/-- The homogeneous coordinate Y on the Weierstrass quotient, as a degree-one element. -/
private def familyYHomogeneous : familyGrading 1 :=
  GradedAlgebra.Quotient.componentMap (ProjectiveSpace.grading ring 2) projectiveIdeal.toIdeal 1
    ⟨MvPolynomial.X (1 : Fin 3),
      (MvPolynomial.mem_homogeneousSubmodule 1 (MvPolynomial.X (1 : Fin 3))).mpr
        (MvPolynomial.isHomogeneous_X ring (1 : Fin 3))⟩

/-- The image of the homogeneous coordinate Y in the Weierstrass quotient ring. -/
private def familyY : MvPolynomial (Fin 3) ring ⧸ projectiveIdeal.toIdeal :=
  familyYHomogeneous

/-- Evaluation of homogeneous coordinates at the infinity point (0 : 1 : 0). -/
private def originEval : MvPolynomial (Fin 3) ring →+* ring :=
  MvPolynomial.eval fun i ↦ if i = (1 : Fin 3) then 1 else 0

/-- Evaluation at (0 : 1 : 0) vanishes on the homogeneous Weierstrass ideal. -/
private theorem originEval_eq_zero_of_mem_projectiveIdeal
    (a : MvPolynomial (Fin 3) ring) (ha : a ∈ projectiveIdeal.toIdeal) :
    originEval a = 0 := sorry

/-- Evaluation at (0 : 1 : 0), descended to the homogeneous Weierstrass quotient. -/
private def originEvalQuotient :
    (MvPolynomial (Fin 3) ring ⧸ projectiveIdeal.toIdeal) →+* ring :=
  Ideal.Quotient.lift projectiveIdeal.toIdeal originEval
    originEval_eq_zero_of_mem_projectiveIdeal

/-- Evaluation of a polynomial class at (0 : 1 : 0) is evaluation of that polynomial. -/
private theorem originEvalQuotient_apply (a : MvPolynomial (Fin 3) ring) :
    originEvalQuotient (Ideal.Quotient.mk projectiveIdeal.toIdeal a) = originEval a :=
  Ideal.Quotient.lift_mk projectiveIdeal.toIdeal originEval originEval_eq_zero_of_mem_projectiveIdeal

/-- Evaluation at (0 : 1 : 0) sends the homogeneous coordinate Y to a unit. -/
private theorem originEval_familyY_isUnit : IsUnit (originEvalQuotient familyY) := sorry

-- Canonical instance search for the localized quotient exceeds the default budget.
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
/-- Evaluation of homogeneous fractions at (0 : 1 : 0) preserves one, multiplication,
zero, and addition. -/
private theorem originAwayHom_laws :
    let f : Away familyGrading familyY → ring := fun x ↦
      originEvalQuotient (HomogeneousLocalization.num x) *
        Ring.inverse (originEvalQuotient (HomogeneousLocalization.den x))
    f 1 = 1 ∧ (∀ a b, f (a * b) = f a * f b) ∧
      f 0 = 0 ∧ (∀ a b, f (a + b) = f a + f b) := sorry

-- Canonical instance search for the localized quotient exceeds the default budget.
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
/-- The ring homomorphism from the Y-chart to the coefficient ring given by evaluation
at the infinity point (0 : 1 : 0). -/
private def originAwayHom : Away familyGrading familyY →+* ring where
  toFun x :=
    originEvalQuotient (HomogeneousLocalization.num x) *
      Ring.inverse (originEvalQuotient (HomogeneousLocalization.den x))
  map_one' := originAwayHom_laws.1
  map_mul' := originAwayHom_laws.2.1
  map_zero' := originAwayHom_laws.2.2.1
  map_add' := originAwayHom_laws.2.2.2

/-- The Y-chart evaluation at (0 : 1 : 0) is evaluation of the homogeneous
numerator and denominator. -/
private theorem originAwayHom_apply (x : Away familyGrading familyY) :
    originAwayHom x =
      originEvalQuotient (HomogeneousLocalization.num x) *
        Ring.inverse (originEvalQuotient (HomogeneousLocalization.den x)) :=
  rfl

-- Canonical instance search for the localized quotient exceeds the default budget.
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
/-- The infinity section 0_W : W to E_W given by (0 : 1 : 0) on the Y-chart. -/
def familyZero : scheme.{u} ⟶ familyTotal.{u} :=
  Spec.map (CommRingCat.ofHom originAwayHom) ≫
    Proj.awayι familyGrading familyY familyYHomogeneous.property Nat.zero_lt_one

/-- The infinity section is a section of the projection f_W. -/
theorem familyZero_isSection : familyZero.{u} ≫ familyHom.{u} = 𝟙 scheme.{u} := sorry

/-- The universal Weierstrass family (E_W, f_W, 0_W) is an elliptic curve over W. -/
instance instIsEllipticCurve :
    EllipticCurve.IsEllipticCurve (Over.mk familyHom.{u}) familyZero.{u} := sorry

/-- The classifying 1-morphism of the universal Weierstrass family into the moduli stack of
elliptic curves. -/
@[expose]
def classifying : GroupoidsOver.slice overInt.{u} ⟶ EllipticCurve.moduli.{u} :=
  @EllipticCurve.Moduli.classifying overInt.{u} (Over.mk familyHom.{u}) familyZero.{u}
    instIsEllipticCurve

/-- The infinity section splits the universal Weierstrass projection, which is proper
and smooth of relative dimension one. -/
theorem family_spec :
    familyZero.{u} ≫ familyHom.{u} = 𝟙 scheme.{u} ∧
      IsProper familyHom.{u} ∧ SmoothOfRelativeDimension 1 familyHom.{u} := by
  have h := EllipticCurve.IsEllipticCurve.spec (Over.mk familyHom.{u}) familyZero.{u}
  exact ⟨h.1, h.2.1, h.2.2.1⟩

end AlgebraicGeometry.WeierstrassScheme
