module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.Localization.Away.Basic
public import ReasLib.RingTheory.LocalRing.Nodal
public import ReasLib.RingTheory.Ideal.AssociatedGraded.DegreeZero

@[expose] public section

noncomputable section

open IsLocalRing Polynomial

universe u

namespace NodalLocalRing

variable (A : Type u) [CommRing A] [IsLocalRing A]
variable (e : Module.Basis (Fin 2) (ResidueField A) (CotangentSpace A))

/-- The degree-one tangent-cone coordinate corresponding to a cotangent basis vector. -/
def tangentCoordinate (i : Fin 2) : Ideal.AssociatedGraded.grade (maximalIdeal A) 1 :=
  idealConormalDegreeOne (maximalIdeal A) (e i)

/-- The affine tangent-cone chart on which the second cotangent coordinate is invertible. -/
abbrev tangentChart : Type u :=
  HomogeneousLocalization.Away (Ideal.AssociatedGraded.grade (maximalIdeal A))
    (tangentCoordinate A e 1).1

/-- The residue-field homomorphism to the affine tangent-cone chart. -/
def tangentChartScalarMap : ResidueField A →+* tangentChart A e :=
  (HomogeneousLocalization.fromZeroRingHom
    (Ideal.AssociatedGraded.grade (maximalIdeal A)) _).comp
    ((GradedRing.projZeroRingHom'
      (Ideal.AssociatedGraded.grade (maximalIdeal A))).comp
      (algebraMap (ResidueField A) (Ideal.AssociatedGraded.ring (maximalIdeal A))))

/-- The canonical residue-field algebra structure on the affine tangent-cone chart. -/
instance tangentChartAlgebra : Algebra (ResidueField A) (tangentChart A e) :=
  (tangentChartScalarMap A e).toAlgebra

/-- The ratio of the first cotangent coordinate to the second on the affine tangent-cone chart. -/
def tangentChartRoot : tangentChart A e :=
  HomogeneousLocalization.mk
    ⟨1, tangentCoordinate A e 0, tangentCoordinate A e 1,
      ⟨1, pow_one (tangentCoordinate A e 1).1⟩⟩

/-- A quadratic conormal relation vanishes at the ratio of cotangent coordinates. -/
theorem tangentChartRoot_eval (a b c : ResidueField A)
    (h_relation :
      idealConormalAlgebraQuotient (maximalIdeal A)
          (a • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) ^ 2 +
            b • (SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) *
              SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1)) +
            c • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1) ^ 2) = 0) :
    (C a * X ^ 2 + C b * X + C c).eval₂ (tangentChartScalarMap A e)
      (tangentChartRoot A e) = 0 := sorry

/-- The coordinate comparison from a quadratic presentation to its affine tangent-cone chart. -/
def quadraticPresentationToTangentChart (a b c : ResidueField A)
    (h_relation :
      idealConormalAlgebraQuotient (maximalIdeal A)
          (a • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) ^ 2 +
            b • (SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) *
              SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1)) +
            c • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1) ^ 2) = 0) :
    AdjoinRoot (C a * X ^ 2 + C b * X + C c) →ₐ[ResidueField A] tangentChart A e :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) (tangentChartRoot A e)
    (tangentChartRoot_eval A e a b c h_relation)

/-- Evaluation of symmetric cotangent tensors in quadratic coordinates. -/
def symmetricQuadraticEvaluation (a b c : ResidueField A) :
    SymmetricAlgebra (ResidueField A) (CotangentSpace A) →ₐ[ResidueField A]
      AdjoinRoot (C a * X ^ 2 + C b * X + C c) :=
  SymmetricAlgebra.lift
    ((e.coord 0).smulRight (AdjoinRoot.root (C a * X ^ 2 + C b * X + C c)) +
      (e.coord 1).smulRight 1)

/-- Quadratic coordinate evaluation annihilates the conormal kernel at a node. -/
theorem symmetricQuadraticEvaluation_ker [IsNodalLocalRing A]
    (a b c : ResidueField A) (ha : a ≠ 0)
    (h_relation :
      idealConormalAlgebraQuotient (maximalIdeal A)
          (a • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) ^ 2 +
            b • (SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) *
              SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1)) +
            c • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1) ^ 2) = 0) :
    RingHom.ker (idealConormalAlgebraQuotient (maximalIdeal A)).toRingHom ≤
      RingHom.ker (symmetricQuadraticEvaluation A e a b c).toRingHom := sorry

/-- The tangent-cone evaluation sending the first cotangent coordinate to the quadratic root
and the second to one. -/
def tangentConeEvaluation [IsNodalLocalRing A]
    (a b c : ResidueField A) (ha : a ≠ 0)
    (h_relation :
      idealConormalAlgebraQuotient (maximalIdeal A)
          (a • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) ^ 2 +
            b • (SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) *
              SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1)) +
            c • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1) ^ 2) = 0) :
    Ideal.AssociatedGraded.ring (maximalIdeal A) →ₐ[ResidueField A]
      AdjoinRoot (C a * X ^ 2 + C b * X + C c) where
  __ := (idealConormalAlgebraQuotient (maximalIdeal A)).toRingHom.liftOfSurjective
    (idealConormalAlgebraQuotient_surjective (maximalIdeal A))
    ⟨(symmetricQuadraticEvaluation A e a b c).toRingHom,
      symmetricQuadraticEvaluation_ker A e a b c ha h_relation⟩
  commutes' := by
    intro r
    sorry

/-- The second cotangent coordinate evaluates to one. -/
theorem tangentConeEvaluation_secondCoordinate [IsNodalLocalRing A]
    (a b c : ResidueField A) (ha : a ≠ 0)
    (h_relation :
      idealConormalAlgebraQuotient (maximalIdeal A)
          (a • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) ^ 2 +
            b • (SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) *
              SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1)) +
            c • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1) ^ 2) = 0) :
    tangentConeEvaluation A e a b c ha h_relation (tangentCoordinate A e 1) = 1 := sorry

/-- The reverse coordinate map from the affine tangent-cone chart to the quadratic algebra. -/
def quadraticPresentationFromTangentChart [IsNodalLocalRing A]
    (a b c : ResidueField A) (ha : a ≠ 0)
    (h_relation :
      idealConormalAlgebraQuotient (maximalIdeal A)
          (a • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) ^ 2 +
            b • (SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) *
              SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1)) +
            c • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1) ^ 2) = 0) :
    tangentChart A e →ₐ[ResidueField A] AdjoinRoot (C a * X ^ 2 + C b * X + C c) where
  __ := (IsLocalization.Away.lift (S := Localization.Away (tangentCoordinate A e 1).1)
      (tangentCoordinate A e 1).1
      (g := (tangentConeEvaluation A e a b c ha h_relation).toRingHom)
      (by
        change IsUnit (tangentConeEvaluation A e a b c ha h_relation (tangentCoordinate A e 1))
        rw [tangentConeEvaluation_secondCoordinate A e a b c ha h_relation]
        exact isUnit_one)).comp
    (algebraMap (tangentChart A e) (Localization.Away (tangentCoordinate A e 1).1))
  commutes' := by
    intro r
    sorry

/-- The two quadratic tangent-chart comparison maps are inverse on the chart. -/
theorem quadraticPresentationToFromTangentChart [IsNodalLocalRing A]
    (a b c : ResidueField A) (ha : a ≠ 0)
    (h_relation :
      idealConormalAlgebraQuotient (maximalIdeal A)
          (a • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) ^ 2 +
            b • (SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) *
              SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1)) +
            c • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1) ^ 2) = 0) :
    (quadraticPresentationToTangentChart A e a b c h_relation).comp
        (quadraticPresentationFromTangentChart A e a b c ha h_relation) =
      AlgHom.id (ResidueField A) (tangentChart A e) := sorry

/-- The two quadratic tangent-chart comparison maps are inverse on the quadratic algebra. -/
theorem quadraticPresentationFromToTangentChart [IsNodalLocalRing A]
    (a b c : ResidueField A) (ha : a ≠ 0)
    (h_relation :
      idealConormalAlgebraQuotient (maximalIdeal A)
          (a • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) ^ 2 +
            b • (SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) *
              SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1)) +
            c • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1) ^ 2) = 0) :
    (quadraticPresentationFromTangentChart A e a b c ha h_relation).comp
        (quadraticPresentationToTangentChart A e a b c h_relation) =
      AlgHom.id (ResidueField A) (AdjoinRoot (C a * X ^ 2 + C b * X + C c)) := sorry

/-- A valid nodal quadratic presentation identifies its root algebra with the affine
chart of the projectivized tangent cone where the second coordinate is nonzero. -/
def quadraticPresentationTangentChartEquiv [IsNodalLocalRing A]
    (a b c : ResidueField A) (ha : a ≠ 0)
    (h_relation :
      idealConormalAlgebraQuotient (maximalIdeal A)
          (a • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) ^ 2 +
            b • (SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) *
              SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1)) +
            c • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1) ^ 2) = 0) :
    AdjoinRoot (C a * X ^ 2 + C b * X + C c) ≃ₐ[ResidueField A] tangentChart A e :=
  AlgEquiv.ofAlgHom (quadraticPresentationToTangentChart A e a b c h_relation)
    (quadraticPresentationFromTangentChart A e a b c ha h_relation)
    (quadraticPresentationToFromTangentChart A e a b c ha h_relation)
    (quadraticPresentationFromToTangentChart A e a b c ha h_relation)

section Computation

variable (a b c : ResidueField A)
variable (h_relation :
  idealConormalAlgebraQuotient (maximalIdeal A)
      (a • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) ^ 2 +
        b • (SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) *
          SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1)) +
        c • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1) ^ 2) = 0)

/-- The quadratic generator maps to the ratio of the cotangent coordinates. -/
@[simp]
theorem quadraticPresentationToTangentChart_root :
    quadraticPresentationToTangentChart A e a b c h_relation
      (AdjoinRoot.root (C a * X ^ 2 + C b * X + C c)) = tangentChartRoot A e :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

variable [IsNodalLocalRing A] (ha : a ≠ 0)

/-- The forward map of the chart equivalence is the coordinate-ratio homomorphism. -/
@[simp]
theorem quadraticPresentationTangentChartEquiv_toAlgHom :
    (quadraticPresentationTangentChartEquiv A e a b c ha h_relation).toAlgHom =
      quadraticPresentationToTangentChart A e a b c h_relation := rfl

/-- The inverse map of the chart equivalence is the localized coordinate evaluation. -/
@[simp]
theorem quadraticPresentationTangentChartEquiv_symm_toAlgHom :
    (quadraticPresentationTangentChartEquiv A e a b c ha h_relation).symm.toAlgHom =
      quadraticPresentationFromTangentChart A e a b c ha h_relation := rfl

end Computation

end NodalLocalRing
