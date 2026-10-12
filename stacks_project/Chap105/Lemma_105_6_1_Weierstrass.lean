/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
public import ReasLib.RingTheory.GradedAlgebra.Quotient
public import stacks_project.Chap105.Definition_105_5_1_Moduli

/-!
# The Weierstrass scheme

The affine scheme W = Spec of the localized Weierstrass ring, carrying the universal cubic,
its projection, and the infinity section (0 : 1 : 0).
-/

@[expose] public section

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
def universal : WeierstrassCurve coeffRing where
  a₁ := MvPolynomial.X ⟨.a1⟩
  a₂ := MvPolynomial.X ⟨.a2⟩
  a₃ := MvPolynomial.X ⟨.a3⟩
  a₄ := MvPolynomial.X ⟨.a4⟩
  a₆ := MvPolynomial.X ⟨.a6⟩

/-- The discriminant Δ of the universal Weierstrass curve. -/
def Δ : coeffRing :=
  universal.Δ

/-- The discriminant is the discriminant of the universal Weierstrass curve. -/
theorem Δ_eq : Δ = universal.Δ := sorry

/-- The coordinate ring of the Weierstrass scheme, obtained by inverting Δ. -/
abbrev ring : Type u :=
  Localization.Away Δ

/-- The Weierstrass curve with coefficients in the localized ring. -/
def curve : WeierstrassCurve ring :=
  universal.map (algebraMap coeffRing ring)

/-- The homogeneous Weierstrass cubic on P2 over the localized ring. -/
def projectivePolynomial : MvPolynomial (Fin 3) ring :=
  WeierstrassCurve.Projective.polynomial curve

/-- The homogeneous ideal of the universal Weierstrass cubic. -/
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

/-- The Weierstrass quotient grading is a graded monoid. -/
instance familyGrading_gradedMonoid : SetLike.GradedMonoid familyGrading :=
  GradedAlgebra.Quotient.setLikeGradedMonoid (ProjectiveSpace.grading ring 2)
    projectiveIdeal.toIdeal

/-- The Weierstrass scheme W as Spec of the localized coefficient ring. -/
def scheme : Scheme.{u} :=
  Spec (.of ring)

/-- The Weierstrass scheme is the spectrum of the localized coefficient ring. -/
theorem scheme_eq : scheme = Spec (.of ring) := sorry

/-- The integral base Spec(ULift ℤ) used by the moduli stack of elliptic curves. -/
abbrev specInt : Scheme.{u} :=
  EllipticCurve.Moduli.specInt

/-- The structure morphism W to Spec ℤ. -/
def toSpecInt : scheme ⟶ specInt :=
  Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) ring))

/-- The Weierstrass scheme as an object of the slice over Spec ℤ. -/
def overInt : Over specInt :=
  Over.mk toSpecInt

/-- The total space E_W of the universal Weierstrass family, realized as the projective spectrum
of the homogeneous quotient by the Weierstrass cubic. -/
def familyTotal : Scheme.{u} :=
  Proj familyGrading

/-- Constants as a ring homomorphism into the degree-zero piece of the Weierstrass quotient. -/
def ringToDegreeZero : ring →+* familyGrading 0 where
  toFun r :=
    GradedAlgebra.Quotient.componentMap (ProjectiveSpace.grading ring 2)
      projectiveIdeal.toIdeal 0 (ProjectiveSpace.degreeZeroC ring 2 r)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- The projection f_W : E_W to W, as the structure morphism of Proj of the Weierstrass
quotient. -/
def familyHom : familyTotal ⟶ scheme :=
  Proj.toSpecZero familyGrading ≫ Spec.map (CommRingCat.ofHom ringToDegreeZero)

/-- The homogeneous coordinate Y on the Weierstrass quotient, as a degree-one element. -/
def familyYHomogeneous : familyGrading 1 :=
  GradedAlgebra.Quotient.componentMap (ProjectiveSpace.grading ring 2) projectiveIdeal.toIdeal 1
    ⟨MvPolynomial.X (1 : Fin 3),
      (MvPolynomial.mem_homogeneousSubmodule 1 (MvPolynomial.X (1 : Fin 3))).mpr
        (MvPolynomial.isHomogeneous_X ring (1 : Fin 3))⟩

/-- The image of the homogeneous coordinate Y in the Weierstrass quotient ring. -/
def familyY : MvPolynomial (Fin 3) ring ⧸ projectiveIdeal.toIdeal :=
  familyYHomogeneous

/-- The Y-chart ring of the Weierstrass quotient is a commutative ring. -/
instance familyYAwayCommRing : CommRing (Away familyGrading familyY) :=
  HomogeneousLocalization.homogeneousLocalizationCommRing

/-- Evaluation of homogeneous coordinates at the infinity point (0 : 1 : 0). -/
def originEval : MvPolynomial (Fin 3) ring →+* ring :=
  MvPolynomial.eval fun i ↦ if i = (1 : Fin 3) then 1 else 0

/-- Evaluation at (0 : 1 : 0) vanishes on the homogeneous Weierstrass ideal. -/
theorem originEval_eq_zero_of_mem_projectiveIdeal
    (a : MvPolynomial (Fin 3) ring) (ha : a ∈ projectiveIdeal.toIdeal) :
    originEval a = 0 := sorry

/-- Evaluation at (0 : 1 : 0), descended to a chosen representative of the
homogeneous Weierstrass quotient. -/
def originEvalQuotient :
    (MvPolynomial (Fin 3) ring ⧸ projectiveIdeal.toIdeal) →+* ring where
  toFun a := originEval (Quotient.out a)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- Evaluation at (0 : 1 : 0) on the quotient is evaluation of a chosen
polynomial representative. -/
theorem originEvalQuotient_apply
    (a : MvPolynomial (Fin 3) ring ⧸ projectiveIdeal.toIdeal) :
    originEvalQuotient a = originEval (Quotient.out a) := sorry

/-- Evaluation at (0 : 1 : 0) sends the homogeneous coordinate Y to a unit. -/
theorem originEval_familyY_isUnit : IsUnit (originEvalQuotient familyY) := sorry

/-- The ring homomorphism from the Y-chart of E_W to W sending the origin of the
dehomogenized coordinates to (0 : 1 : 0). -/
def originAwayHom : Away familyGrading familyY →+* ring where
  toFun x :=
    originEvalQuotient (HomogeneousLocalization.num x) *
      Ring.inverse (originEvalQuotient (HomogeneousLocalization.den x))
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- The Y-chart evaluation at (0 : 1 : 0) is evaluation of the homogeneous
numerator and denominator. -/
theorem originAwayHom_apply (x : Away familyGrading familyY) :
    originAwayHom x =
      originEvalQuotient (HomogeneousLocalization.num x) *
        Ring.inverse (originEvalQuotient (HomogeneousLocalization.den x)) :=
  sorry

/-- The infinity section 0_W : W to E_W given by (0 : 1 : 0) on the Y-chart. -/
def familyZero : scheme ⟶ familyTotal :=
  Spec.map (CommRingCat.ofHom originAwayHom) ≫
    Proj.awayι familyGrading familyY familyYHomogeneous.property Nat.zero_lt_one

/-- The infinity section is a section of the projection f_W. -/
theorem familyZero_isSection : familyZero ≫ familyHom = 𝟙 scheme := sorry

/-- The universal Weierstrass family (E_W, f_W, 0_W) is an elliptic curve over W. -/
instance instIsEllipticCurve :
    EllipticCurve.IsEllipticCurve (Over.mk familyHom) familyZero := sorry

/-- The classifying 1-morphism of the universal Weierstrass family into the moduli stack of
elliptic curves. -/
def classifying : GroupoidsOver.slice overInt ⟶ EllipticCurve.moduli :=
  @EllipticCurve.Moduli.classifying overInt (Over.mk familyHom) familyZero instIsEllipticCurve

/-- classifying is the classifying 1-morphism of (E_W, f_W, 0_W). -/
theorem classifying_eq :
    classifying =
      @EllipticCurve.Moduli.classifying overInt (Over.mk familyHom) familyZero
        instIsEllipticCurve := sorry

/-- The source conditions on (E_W, f_W, 0_W): the infinity section splits f_W, which is proper
and smooth of relative dimension 1. -/
theorem family_spec :
    familyZero ≫ familyHom = 𝟙 scheme ∧
      IsProper familyHom ∧ SmoothOfRelativeDimension 1 familyHom := sorry

end AlgebraicGeometry.WeierstrassScheme
