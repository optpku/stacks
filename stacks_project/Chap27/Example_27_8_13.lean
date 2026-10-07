module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.SquareRootTower

@[expose] public section

open AlgebraicGeometry

/- Example 27.8.13

For the powers-of-two graded quotient by `Xᵢ² - tXᵢ₊₁`, the parameter `t`
avoids the projective points, the variable standard opens cover and agree
successively, the first such open is the entire affine projective spectrum,
and the resulting quasi-compact morphism to `Spec(ℂ[t])` has image `D(t)`, is
not closed, and fails the existence part of the valuative criterion.
-/
@[stacks 01MH] #check
  (AlgebraicGeometry.squareRootTowerExample :
    (∀ x : Proj squareRootTowerQuotientGrading,
      squareRootTowerParameter ∉ x.asHomogeneousIdeal) ∧
    (⨆ i : ℕ, Proj.basicOpen squareRootTowerQuotientGrading
      (squareRootTowerVariable i)) = ⊤ ∧
    (∀ i : ℕ, Proj.basicOpen squareRootTowerQuotientGrading
      (squareRootTowerVariable i) =
        Proj.basicOpen squareRootTowerQuotientGrading
          (squareRootTowerVariable (i + 1))) ∧
    Proj.basicOpen squareRootTowerQuotientGrading (squareRootTowerVariable 0) = ⊤ ∧
    IsAffine (Proj squareRootTowerQuotientGrading) ∧
    QuasiCompact squareRootTowerProjToSpec ∧
    Set.range squareRootTowerProjToSpec.base =
      (PrimeSpectrum.basicOpen squareRootTower_t :
        Set (PrimeSpectrum squareRootTowerBaseRing)) ∧
    ¬ IsClosedMap squareRootTowerProjToSpec.base ∧
    ¬ ValuativeCriterion.Existence squareRootTowerProjToSpec)

universe u v w

#check (AlgebraicGeometry.squareRootTowerBaseRing : Type)

#check (AlgebraicGeometry.squareRootTowerAmbientRing : Type)

#check (AlgebraicGeometry.squareRootTower_t :
  AlgebraicGeometry.squareRootTowerBaseRing)

#check (AlgebraicGeometry.squareRootTowerWeight : ℕ → ℕ)

#check (AlgebraicGeometry.squareRootTowerPolynomialGrading :
  ℕ → Submodule AlgebraicGeometry.squareRootTowerBaseRing
    AlgebraicGeometry.squareRootTowerAmbientRing)

#check (AlgebraicGeometry.squareRootTowerRelation :
  ℕ → AlgebraicGeometry.squareRootTowerAmbientRing)

#check (AlgebraicGeometry.squareRootTowerIdeal :
  Ideal AlgebraicGeometry.squareRootTowerAmbientRing)

#check (AlgebraicGeometry.squareRootTowerRing : Type)

#check (AlgebraicGeometry.squareRootTowerQuotientMap :
  AlgebraicGeometry.squareRootTowerAmbientRing →ₐ[
    AlgebraicGeometry.squareRootTowerBaseRing]
      AlgebraicGeometry.squareRootTowerRing)

#check (AlgebraicGeometry.squareRootTowerQuotientGrading :
  ℕ → Submodule AlgebraicGeometry.squareRootTowerBaseRing
    AlgebraicGeometry.squareRootTowerRing)

#check (AlgebraicGeometry.squareRootTowerRelation_mem_polynomialGrading :
  ∀ i : ℕ, AlgebraicGeometry.squareRootTowerRelation i ∈
    AlgebraicGeometry.squareRootTowerPolynomialGrading (2 ^ (i + 1)))

#check (AlgebraicGeometry.squareRootTowerIdeal_isHomogeneous :
  AlgebraicGeometry.squareRootTowerIdeal.IsHomogeneous
    AlgebraicGeometry.squareRootTowerPolynomialGrading)

#check (SetLike.GradeZero.instCommRing :
  ∀ {i : Type u} {S : Type v} {B : Type w}
    [CommRing B] [AddCommMonoid i] [SetLike S B] [AddSubgroupClass S B]
    (A : i → S) [SetLike.GradedMonoid A], CommRing (A 0))

#check (GradedAlgebra.Quotient.setLikeGradedMonoid :
  ∀ {i : Type u} {R : Type v} {A : Type w}
    [CommSemiring R] [Ring A] [Algebra R A]
    (𝒜 : i → Submodule R A) (J : Ideal A) [J.IsTwoSided]
    [DecidableEq i] [AddMonoid i] [GradedAlgebra 𝒜],
      SetLike.GradedMonoid (GradedAlgebra.Quotient.grading 𝒜 J))

#check (GradedAlgebra.Quotient.componentMap :
  ∀ {i : Type u} {R : Type v} {A : Type w}
    [CommSemiring R] [Ring A] [Algebra R A]
    (𝒜 : i → Submodule R A) (J : Ideal A) [J.IsTwoSided]
    (n : i), 𝒜 n →ₗ[R] GradedAlgebra.Quotient.grading 𝒜 J n)

#check (GradedAlgebra.Quotient.directSumComponentMap_one :
  ∀ {i : Type u} {R : Type v} {A : Type w}
    [CommSemiring R] [Ring A] [Algebra R A]
    (𝒜 : i → Submodule R A) (J : Ideal A) [J.IsTwoSided]
    [DecidableEq i] [AddMonoid i] [GradedAlgebra 𝒜],
      (DirectSum.lof R i
        (fun n ↦ GradedAlgebra.Quotient.grading 𝒜 J n) 0)
          (GradedAlgebra.Quotient.componentMap 𝒜 J 0
            ⟨1, SetLike.one_mem_graded 𝒜⟩) = 1)

#check (GradedAlgebra.Quotient.directSumComponentMap_mul :
  ∀ {i : Type u} {R : Type v} {A : Type w}
    [CommSemiring R] [Ring A] [Algebra R A]
    (𝒜 : i → Submodule R A) (J : Ideal A) [J.IsTwoSided]
    [DecidableEq i] [AddMonoid i] [GradedAlgebra 𝒜]
    {m n : i} (x : 𝒜 m) (y : 𝒜 n),
      (DirectSum.lof R i
        (fun k ↦ GradedAlgebra.Quotient.grading 𝒜 J k) (m + n))
          (GradedAlgebra.Quotient.componentMap 𝒜 J (m + n)
            ⟨x.1 * y.1, SetLike.mul_mem_graded x.2 y.2⟩) =
        (DirectSum.lof R i
          (fun k ↦ GradedAlgebra.Quotient.grading 𝒜 J k) m)
            (GradedAlgebra.Quotient.componentMap 𝒜 J m x) *
          (DirectSum.lof R i
            (fun k ↦ GradedAlgebra.Quotient.grading 𝒜 J k) n)
              (GradedAlgebra.Quotient.componentMap 𝒜 J n y))

#check (GradedAlgebra.Quotient.directSumAlgHom :
  ∀ {i : Type u} {R : Type v} {A : Type w}
    [CommSemiring R] [Ring A] [Algebra R A]
    (𝒜 : i → Submodule R A) (J : Ideal A) [J.IsTwoSided]
    [DecidableEq i] [AddMonoid i] [GradedAlgebra 𝒜],
      DirectSum i (fun n ↦ 𝒜 n) →ₐ[R]
        DirectSum i (fun n ↦ GradedAlgebra.Quotient.grading 𝒜 J n))

#check (GradedAlgebra.Quotient.predecomposeAlgHom :
  ∀ {i : Type u} {R : Type v} {A : Type w}
    [CommSemiring R] [Ring A] [Algebra R A]
    (𝒜 : i → Submodule R A) (J : Ideal A) [J.IsTwoSided]
    [DecidableEq i] [AddMonoid i] [GradedAlgebra 𝒜],
      A →ₐ[R]
        DirectSum i (fun n ↦ GradedAlgebra.Quotient.grading 𝒜 J n))

#check (GradedAlgebra.Quotient.predecomposeAlgHom_eq_zero_of_mem :
  ∀ {i : Type u} {R : Type v} {A : Type w}
    [CommSemiring R] [Ring A] [Algebra R A]
    (𝒜 : i → Submodule R A) (J : Ideal A) [J.IsTwoSided]
    [DecidableEq i] [AddMonoid i] [GradedAlgebra 𝒜]
    (_hJ : J.IsHomogeneous 𝒜) (a : A) (_ha : a ∈ J),
      GradedAlgebra.Quotient.predecomposeAlgHom 𝒜 J a = 0)

#check (GradedAlgebra.Quotient.decomposeAlgHom :
  ∀ {i : Type u} {R : Type v} {A : Type w}
    [CommSemiring R] [Ring A] [Algebra R A]
    (𝒜 : i → Submodule R A) (J : Ideal A) [J.IsTwoSided]
    [DecidableEq i] [AddMonoid i] [GradedAlgebra 𝒜]
    (_hJ : J.IsHomogeneous 𝒜),
      A ⧸ J →ₐ[R]
        DirectSum i (fun n ↦ GradedAlgebra.Quotient.grading 𝒜 J n))

#check (GradedAlgebra.Quotient.decomposeAlgHom_right_inv :
  ∀ {i : Type u} {R : Type v} {A : Type w}
    [CommSemiring R] [Ring A] [Algebra R A]
    (𝒜 : i → Submodule R A) (J : Ideal A) [J.IsTwoSided]
    [DecidableEq i] [AddMonoid i] [GradedAlgebra 𝒜]
    (hJ : J.IsHomogeneous 𝒜),
      (DirectSum.coeAlgHom (GradedAlgebra.Quotient.grading 𝒜 J)).comp
          (GradedAlgebra.Quotient.decomposeAlgHom 𝒜 J hJ) =
        AlgHom.id R (A ⧸ J))

#check (GradedAlgebra.Quotient.decomposeAlgHom_left_inv :
  ∀ {i : Type u} {R : Type v} {A : Type w}
    [CommSemiring R] [Ring A] [Algebra R A]
    (𝒜 : i → Submodule R A) (J : Ideal A) [J.IsTwoSided]
    [DecidableEq i] [AddMonoid i] [GradedAlgebra 𝒜]
    (hJ : J.IsHomogeneous 𝒜) (n : i)
    (x : GradedAlgebra.Quotient.grading 𝒜 J n),
      GradedAlgebra.Quotient.decomposeAlgHom 𝒜 J hJ (x : A ⧸ J) =
        DirectSum.of
          (fun k ↦ GradedAlgebra.Quotient.grading 𝒜 J k) n x)

#check (AlgebraicGeometry.squareRootTowerQuotientGradedAlgebra :
  GradedAlgebra AlgebraicGeometry.squareRootTowerQuotientGrading)

#check (AlgebraicGeometry.squareRootTowerDegreeZeroSubring :
  Subring AlgebraicGeometry.squareRootTowerRing)

#check (AlgebraicGeometry.squareRootTowerConstantClass_mem_degreeZero :
  ∀ r : AlgebraicGeometry.squareRootTowerBaseRing,
    algebraMap AlgebraicGeometry.squareRootTowerBaseRing
      AlgebraicGeometry.squareRootTowerRing r ∈
        AlgebraicGeometry.squareRootTowerDegreeZeroSubring)

#check (AlgebraicGeometry.squareRootTowerDegreeZeroAlgebraMap :
  AlgebraicGeometry.squareRootTowerBaseRing →+*
    AlgebraicGeometry.squareRootTowerDegreeZeroSubring)

#check (AlgebraicGeometry.squareRootTowerDegreeZeroAlgebraMap_injective :
  Function.Injective AlgebraicGeometry.squareRootTowerDegreeZeroAlgebraMap)

#check (AlgebraicGeometry.squareRootTowerDegreeZeroAlgebraMap_surjective :
  Function.Surjective AlgebraicGeometry.squareRootTowerDegreeZeroAlgebraMap)

#check (AlgebraicGeometry.squareRootTowerDegreeZeroRingEquiv :
  AlgebraicGeometry.squareRootTowerDegreeZeroSubring ≃+*
    AlgebraicGeometry.squareRootTowerBaseRing)

#check (AlgebraicGeometry.squareRootTowerDegreeZeroSpecIso :
  AlgebraicGeometry.Spec
      (.of AlgebraicGeometry.squareRootTowerDegreeZeroSubring) ≅
    AlgebraicGeometry.Spec
      (.of AlgebraicGeometry.squareRootTowerBaseRing))

#check (AlgebraicGeometry.squareRootTowerProjToSpec :
  AlgebraicGeometry.Proj
      AlgebraicGeometry.squareRootTowerQuotientGrading ⟶
    AlgebraicGeometry.Spec
      (.of AlgebraicGeometry.squareRootTowerBaseRing))

#check (AlgebraicGeometry.squareRootTowerProjToSpec_range_eq_basicOpen :
  Set.range AlgebraicGeometry.squareRootTowerProjToSpec.base =
    (PrimeSpectrum.basicOpen AlgebraicGeometry.squareRootTower_t :
      Set (PrimeSpectrum AlgebraicGeometry.squareRootTowerBaseRing)))

#check (AlgebraicGeometry.squareRootTowerProj_isAffine :
  AlgebraicGeometry.IsAffine
    (AlgebraicGeometry.Proj
      AlgebraicGeometry.squareRootTowerQuotientGrading))

#check (AlgebraicGeometry.squareRootTowerProjToSpec_quasiCompact :
  AlgebraicGeometry.QuasiCompact
    AlgebraicGeometry.squareRootTowerProjToSpec)

#check (AlgebraicGeometry.projSquareRootTowerToSpec_not_isClosedMap :
  ¬ IsClosedMap AlgebraicGeometry.squareRootTowerProjToSpec.base)

#check (AlgebraicGeometry.projSquareRootTowerToSpec_not_valuativeCriterionExistence :
  ¬ AlgebraicGeometry.ValuativeCriterion.Existence
    AlgebraicGeometry.squareRootTowerProjToSpec)

#check (AlgebraicGeometry.squareRootTowerPolynomialGradedAlgebra :
  GradedAlgebra AlgebraicGeometry.squareRootTowerPolynomialGrading)

#check (AlgebraicGeometry.squareRootTowerVariable :
  ℕ → AlgebraicGeometry.squareRootTowerRing)

#check (AlgebraicGeometry.squareRootTowerParameter :
  AlgebraicGeometry.squareRootTowerRing)

#check (AlgebraicGeometry.squareRootTowerVariable_mem_grading :
  ∀ i : ℕ, AlgebraicGeometry.squareRootTowerVariable i ∈
    AlgebraicGeometry.squareRootTowerQuotientGrading (2 ^ i))

#check (AlgebraicGeometry.squareRootTowerRelation_quotient :
  ∀ i : ℕ, AlgebraicGeometry.squareRootTowerVariable i ^ 2 =
    AlgebraicGeometry.squareRootTowerParameter *
      AlgebraicGeometry.squareRootTowerVariable (i + 1))

#check (AlgebraicGeometry.squareRootTowerProj_iSup_basicOpen_variable_eq_top :
  (⨆ i : ℕ, AlgebraicGeometry.Proj.basicOpen
    AlgebraicGeometry.squareRootTowerQuotientGrading
      (AlgebraicGeometry.squareRootTowerVariable i)) = ⊤)

#check (AlgebraicGeometry.squareRootTowerParameter_not_mem_proj :
  ∀ x : AlgebraicGeometry.Proj
    AlgebraicGeometry.squareRootTowerQuotientGrading,
      AlgebraicGeometry.squareRootTowerParameter ∉ x.asHomogeneousIdeal)

#check (AlgebraicGeometry.squareRootTowerProj_basicOpen_variable_succ_eq :
  ∀ i : ℕ, AlgebraicGeometry.Proj.basicOpen
      AlgebraicGeometry.squareRootTowerQuotientGrading
        (AlgebraicGeometry.squareRootTowerVariable i) =
    AlgebraicGeometry.Proj.basicOpen
      AlgebraicGeometry.squareRootTowerQuotientGrading
        (AlgebraicGeometry.squareRootTowerVariable (i + 1)))

#check (AlgebraicGeometry.squareRootTowerProj_basicOpen_variable_zero_eq_top :
  AlgebraicGeometry.Proj.basicOpen
    AlgebraicGeometry.squareRootTowerQuotientGrading
      (AlgebraicGeometry.squareRootTowerVariable 0) = ⊤)
