module

public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.IsTensorProduct
public import ReasLib.Algebra.Module.Graded.Left.Category
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.GradedEquivariant
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra

/-!
# Graded global sections of equivariant affine modules

This module constructs the weight decomposition on the global sections of a quasi-coherent
module equivariant for the multiplicative-group action associated to an integral grading.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped AlgebraicGeometry Algebra.TensorProduct.Right ChangeOfRings DirectSum MonObj
  MonoidalLeftAction TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GradedSpec.EquivariantSections

variable {A : Type u} [CommRing A] (𝒜 : ℤ → Submodule ℤ A) [GradedAlgebra 𝒜]
variable (D : Scheme.QCoh.Equivariant MultiplicativeGroup.group
  (GradedSpec.action 𝒜))

/-- The `A`-module of global sections of the quasi-coherent module underlying `D`. -/
abbrev sections : ModuleCat A :=
  (AlgebraicGeometry.tildeEquiv (R := CommRingCat.of A)).inverse.obj
    (Scheme.QCoh.Equivariant.obj D)

/-- `sections 𝒜 D` is the inverse image of the underlying quasi-coherent module under the affine
tilde equivalence. -/
theorem sections_def :
    sections 𝒜 D = (AlgebraicGeometry.tildeEquiv (R := CommRingCat.of A)).inverse.obj
      (Scheme.QCoh.Equivariant.obj D) := sorry

/-- Pulling the graded action back along the affine product comparison recovers the spectrum map
induced by the ring coaction. -/
theorem pullbackSpecIso_inv_action :
    (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).inv ≫
        Scheme.QCoh.Equivariant.action MultiplicativeGroup.group
          (GradedSpec.action 𝒜) =
      Spec.map (GradedSpec.coactionRingHom 𝒜) := sorry

/-- Pulling the action projection back along the affine product comparison recovers the spectrum
map induced by the ring projection. -/
theorem pullbackSpecIso_inv_projection :
    (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).inv ≫
        Scheme.QCoh.Equivariant.projection MultiplicativeGroup.group
          (GradedSpec.action 𝒜) =
      Spec.map (GradedSpec.projectionHom A) := sorry

/-- The stored equivariant linearization transported from the action product to the affine
tensor-product spectrum. -/
def affineAlpha :
    (Scheme.QCoh.pullback (Spec.map (GradedSpec.coactionRingHom 𝒜))).obj
        (Scheme.QCoh.Equivariant.obj D) ⟶
      (Scheme.QCoh.pullback (Spec.map (GradedSpec.projectionHom A))).obj
        (Scheme.QCoh.Equivariant.obj D) :=
  eqToHom (congrArg
      (fun f ↦ (Scheme.QCoh.pullback f).obj (Scheme.QCoh.Equivariant.obj D))
      (pullbackSpecIso_inv_action 𝒜).symm) ≫
    (AlgebraicGeometry.GroupoidScheme.pullbackCompIso
      (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).inv
      (Scheme.QCoh.Equivariant.action MultiplicativeGroup.group
        (GradedSpec.action 𝒜))).hom.app (Scheme.QCoh.Equivariant.obj D) ≫
    (Scheme.QCoh.pullback
      (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).inv).map
        (Scheme.QCoh.Equivariant.alpha D) ≫
    (AlgebraicGeometry.GroupoidScheme.pullbackCompIso
      (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).inv
      (Scheme.QCoh.Equivariant.projection MultiplicativeGroup.group
        (GradedSpec.action 𝒜))).inv.app (Scheme.QCoh.Equivariant.obj D) ≫
    eqToHom (congrArg
      (fun f ↦ (Scheme.QCoh.pullback f).obj (Scheme.QCoh.Equivariant.obj D))
      (pullbackSpecIso_inv_projection 𝒜))

/-- `affineAlpha` is exactly the pullback and change-of-rings transport of the
linearization stored in `D`. -/
theorem affineAlpha_eq :
    affineAlpha 𝒜 D =
      eqToHom (congrArg
          (fun f ↦ (Scheme.QCoh.pullback f).obj (Scheme.QCoh.Equivariant.obj D))
          (pullbackSpecIso_inv_action 𝒜).symm) ≫
        (AlgebraicGeometry.GroupoidScheme.pullbackCompIso
          (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).inv
          (Scheme.QCoh.Equivariant.action MultiplicativeGroup.group
            (GradedSpec.action 𝒜))).hom.app (Scheme.QCoh.Equivariant.obj D) ≫
        (Scheme.QCoh.pullback
          (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).inv).map
            (Scheme.QCoh.Equivariant.alpha D) ≫
        (AlgebraicGeometry.GroupoidScheme.pullbackCompIso
          (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).inv
          (Scheme.QCoh.Equivariant.projection MultiplicativeGroup.group
            (GradedSpec.action 𝒜))).inv.app (Scheme.QCoh.Equivariant.obj D) ≫
        eqToHom (congrArg
          (fun f ↦ (Scheme.QCoh.pullback f).obj (Scheme.QCoh.Equivariant.obj D))
          (pullbackSpecIso_inv_projection 𝒜)) := sorry

/-- The affine transport of `affineAlpha` between tildes of the two scalar extensions of global
sections. -/
def tildeLinearization :
    (AlgebraicGeometry.tildeEquiv
      (R := CommRingCat.of
        (LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] A))).functor.obj
          ((ModuleCat.extendScalars (GradedSpec.coactionRingHom 𝒜).hom).obj
            (sections 𝒜 D)) ⟶
      (AlgebraicGeometry.tildeEquiv
        (R := CommRingCat.of
          (LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] A))).functor.obj
            ((ModuleCat.extendScalars (GradedSpec.projectionHom A).hom).obj
              (sections 𝒜 D)) :=
  ObjectProperty.homMk
    ((tilde.ChangeOfRings.Pullback.iso (GradedSpec.coactionRingHom 𝒜)).inv.app
        (sections 𝒜 D) ≫
      ((Scheme.QCoh.pullback (Spec.map (GradedSpec.coactionRingHom 𝒜))).map
        ((AlgebraicGeometry.tildeEquiv (R := CommRingCat.of A)).counitIso.hom.app
          (Scheme.QCoh.Equivariant.obj D))).hom ≫
      (affineAlpha 𝒜 D).hom ≫
      ((Scheme.QCoh.pullback (Spec.map (GradedSpec.projectionHom A))).map
        ((AlgebraicGeometry.tildeEquiv (R := CommRingCat.of A)).counitIso.inv.app
          (Scheme.QCoh.Equivariant.obj D))).hom ≫
      (tilde.ChangeOfRings.Pullback.iso (GradedSpec.projectionHom A)).hom.app
        (sections 𝒜 D))

/-- The scalar-extension linearization on the global-sections module extracted from `D.alpha`. -/
def linearization :
    (ModuleCat.extendScalars (GradedSpec.coactionRingHom 𝒜).hom).obj
        (sections 𝒜 D) ⟶
      (ModuleCat.extendScalars (GradedSpec.projectionHom A).hom).obj
        (sections 𝒜 D) :=
  (AlgebraicGeometry.tildeEquiv
      (R := CommRingCat.of
        (LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] A))).unitIso.hom.app _ ≫
    (AlgebraicGeometry.tildeEquiv
      (R := CommRingCat.of
        (LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] A))).inverse.map
          (tildeLinearization 𝒜 D) ≫
    (AlgebraicGeometry.tildeEquiv
      (R := CommRingCat.of
        (LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] A))).unitIso.inv.app _

/-- Applying affine tilde transport to `linearization` produces the pullback and
change-of-rings transport of the linearization stored by `D`. -/
theorem linearization_recovers_alpha :
    ((AlgebraicGeometry.tildeEquiv
        (R := CommRingCat.of
          (LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] A))).functor.map
            (linearization 𝒜 D)).hom =
      (tilde.ChangeOfRings.Pullback.iso (GradedSpec.coactionRingHom 𝒜)).inv.app
          (sections 𝒜 D) ≫
        ((Scheme.QCoh.pullback (Spec.map (GradedSpec.coactionRingHom 𝒜))).map
          ((AlgebraicGeometry.tildeEquiv (R := CommRingCat.of A)).counitIso.hom.app
            (Scheme.QCoh.Equivariant.obj D))).hom ≫
        (eqToHom (congrArg
            (fun f ↦ (Scheme.QCoh.pullback f).obj (Scheme.QCoh.Equivariant.obj D))
            (pullbackSpecIso_inv_action 𝒜).symm) ≫
          (AlgebraicGeometry.GroupoidScheme.pullbackCompIso
            (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).inv
            (Scheme.QCoh.Equivariant.action MultiplicativeGroup.group
              (GradedSpec.action 𝒜))).hom.app (Scheme.QCoh.Equivariant.obj D) ≫
          (Scheme.QCoh.pullback
            (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).inv).map
              (Scheme.QCoh.Equivariant.alpha D) ≫
          (AlgebraicGeometry.GroupoidScheme.pullbackCompIso
            (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).inv
            (Scheme.QCoh.Equivariant.projection MultiplicativeGroup.group
              (GradedSpec.action 𝒜))).inv.app (Scheme.QCoh.Equivariant.obj D) ≫
          eqToHom (congrArg
            (fun f ↦ (Scheme.QCoh.pullback f).obj (Scheme.QCoh.Equivariant.obj D))
            (pullbackSpecIso_inv_projection 𝒜))).hom ≫
        ((Scheme.QCoh.pullback (Spec.map (GradedSpec.projectionHom A))).map
          ((AlgebraicGeometry.tildeEquiv (R := CommRingCat.of A)).counitIso.inv.app
            (Scheme.QCoh.Equivariant.obj D))).hom ≫
        (tilde.ChangeOfRings.Pullback.iso (GradedSpec.projectionHom A)).hom.app
          (sections 𝒜 D) := sorry

/-- The adjoint Laurent coaction on the global-sections module. -/
def coaction :
    sections 𝒜 D ⟶
      (ModuleCat.restrictScalars (GradedSpec.coactionRingHom 𝒜).hom).obj
        ((ModuleCat.extendScalars (GradedSpec.projectionHom A).hom).obj
          (sections 𝒜 D)) :=
  ModuleCat.ExtendRestrictScalarsAdj.homEquiv
    (GradedSpec.coactionRingHom 𝒜).hom (linearization 𝒜 D)

/-- The coaction is the adjoint transpose of `linearization`. -/
theorem coaction_eq_homEquiv :
    coaction 𝒜 D =
      ModuleCat.ExtendRestrictScalarsAdj.homEquiv
        (GradedSpec.coactionRingHom 𝒜).hom (linearization 𝒜 D) := sorry

/-- The degree-`n` weight space in the global sections of `D`. -/
def grading (n : ℤ) : Submodule ℤ
    (sections 𝒜 D) where
  carrier := {m | coaction 𝒜 D m =
    ((LaurentPolynomial.T n ⊗ₜ[ULift.{u} ℤ] (1 : A)) :
      LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] A) ⊗ₜ[A,
        (GradedSpec.projectionHom A).hom] m}
  zero_mem' := sorry
  add_mem' := sorry
  smul_mem' := sorry

/-- Membership in `grading 𝒜 D n` is the Laurent weight-`n` coaction identity. -/
theorem mem_grading (n : ℤ)
    (m : sections 𝒜 D) :
    m ∈ grading 𝒜 D n ↔ coaction 𝒜 D m =
      ((LaurentPolynomial.T n ⊗ₜ[ULift.{u} ℤ] (1 : A)) :
        LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] A) ⊗ₜ[A,
          (GradedSpec.projectionHom A).hom] m := sorry

/-- The canonical cancellation and Laurent-basis equivalence used to read off weight
coordinates. -/
def coefficientEquiv :
    (ModuleCat.extendScalars (GradedSpec.projectionHom A).hom).obj
        (sections 𝒜 D) ≃ₗ[ULift.{u} ℤ]
      ℤ →₀ sections 𝒜 D :=
  -- `projectionHom` uses the right tensor factor.
  -- Local instance justification (defeq pin): use `rightAlgebra` to match its source definitionally.
  letI : Algebra A (LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] A) :=
    Algebra.TensorProduct.rightAlgebra
  let rightTower : IsScalarTower (ULift.{u} ℤ) A
      (LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] A) :=
    Algebra.TensorProduct.right_isScalarTower
  let pushout : Algebra.IsPushout (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A
      (LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] A) :=
    TensorProduct.isPushout
  let cancellation :
      (LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] A) ⊗[A]
          sections 𝒜 D ≃ₗ[LaurentPolynomial (ULift.{u} ℤ)]
        LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] sections 𝒜 D :=
    @Algebra.IsPushout.cancelBaseChange
      (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) inferInstance inferInstance
      inferInstance A (LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] A)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      rightTower inferInstance pushout (sections 𝒜 D) inferInstance inferInstance inferInstance
      inferInstance
  cancellation.restrictScalars (ULift.{u} ℤ) ≪≫ₗ
    TensorProduct.equivFinsuppOfBasisLeft
      (AddMonoidAlgebra.basis ℤ (ULift.{u} ℤ))


/-- A pure Laurent monomial in the projection scalar extension has one nonzero coefficient. -/
theorem coefficientEquiv_monomial (n : ℤ) (m : sections 𝒜 D) :
    coefficientEquiv 𝒜 D
        (((LaurentPolynomial.T n ⊗ₜ[ULift.{u} ℤ] (1 : A)) :
          LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] A) ⊗ₜ[A,
            (GradedSpec.projectionHom A).hom] m) =
      Finsupp.single n m := sorry

/-- The finitely supported Laurent coefficients of the coaction of a global section. -/
def coordinates :
    sections 𝒜 D →ₗ[ℤ] ℤ →₀ sections 𝒜 D where
  toFun := fun m ↦ coefficientEquiv 𝒜 D (coaction 𝒜 D m)
  map_add' := sorry
  map_smul' := sorry

/-- Every Laurent coefficient of a section lies in its matching weight space. -/
theorem coordinate_mem_grading
    (m : sections 𝒜 D) (n : ℤ) :
    coordinates 𝒜 D m n ∈ grading 𝒜 D n := sorry

/-- The explicit finite homogeneous decomposition obtained from Laurent coefficients. -/
def homogeneousCoordinates (m : sections 𝒜 D) : ⨁ n : ℤ, grading 𝒜 D n :=
  DFinsupp.mk (coordinates 𝒜 D m).support
    (fun n ↦ ⟨coordinates 𝒜 D m n, coordinate_mem_grading 𝒜 D m n⟩)

/-- The underlying value of `homogeneousCoordinates` in degree `n` is the `n`th Laurent
coefficient. -/
theorem homogeneousCoordinates_apply (m : sections 𝒜 D) (n : ℤ) :
    (homogeneousCoordinates 𝒜 D m n : sections 𝒜 D) = coordinates 𝒜 D m n := sorry

/-- Laurent homogeneous coordinates preserve addition. -/
theorem homogeneousCoordinates_add (m m' : sections 𝒜 D) :
    homogeneousCoordinates 𝒜 D (m + m') =
      homogeneousCoordinates 𝒜 D m + homogeneousCoordinates 𝒜 D m' := sorry

/-- Laurent homogeneous coordinates preserve integer scalar multiplication. -/
theorem homogeneousCoordinates_smul (r : ℤ) (m : sections 𝒜 D) :
    homogeneousCoordinates 𝒜 D (r • m) = r • homogeneousCoordinates 𝒜 D m := sorry

/-- The explicit finite homogeneous decomposition obtained from Laurent coefficients. -/
def decompose : sections 𝒜 D →ₗ[ℤ] (⨁ n : ℤ, grading 𝒜 D n) where
  toFun := homogeneousCoordinates 𝒜 D
  map_add' := homogeneousCoordinates_add 𝒜 D
  map_smul' := homogeneousCoordinates_smul 𝒜 D

/-- Recomposing the Laurent-coordinate decomposition recovers the original section. -/
theorem decompose_left_inv :
    DirectSum.coeLinearMap (grading 𝒜 D) ∘ₗ decompose 𝒜 D = LinearMap.id := sorry

/-- Taking Laurent coordinates after recomposition is the identity on the graded direct sum. -/
theorem decompose_right_inv :
    decompose 𝒜 D ∘ₗ DirectSum.coeLinearMap (grading 𝒜 D) = LinearMap.id := sorry

/-- The canonical direct-sum decomposition of equivariant global sections. -/
noncomputable instance decomposition : DirectSum.Decomposition (grading 𝒜 D) :=
  DirectSum.Decomposition.ofLinearMap (grading 𝒜 D) (decompose 𝒜 D)
    (decompose_left_inv 𝒜 D) (decompose_right_inv 𝒜 D)

/-- The weight decomposition is compatible with the given grading of `A`. -/
instance gradedSMul : SetLike.GradedSMul 𝒜 (grading 𝒜 D) := sorry

/-- The canonically graded `A`-module of global sections of an equivariant quasi-coherent
module. -/
def gradedModule : GradedModule.Left.{0, u, u, 0} 𝒜 ℤ where
  carrier := sections 𝒜 D
  grading := grading 𝒜 D

/-- The grading stored by `gradedModule` is the Laurent weight-space grading. -/
theorem gradedModule_grading : (gradedModule 𝒜 D).grading = grading 𝒜 D := sorry

/-- Forgetting the grading on `gradedModule` recovers the global-sections module. -/
theorem gradedModule_module :
    ModuleCat.of A (gradedModule 𝒜 D) = sections 𝒜 D := sorry

/-- The underlying quasi-coherent-module map of the canonical equivariant counit. -/
def counitHom :
    Scheme.QCoh.Equivariant.obj
        (GradedSpec.equivariantTilde 𝒜 (gradedModule 𝒜 D)) ⟶
      Scheme.QCoh.Equivariant.obj D :=
  eqToHom (GradedSpec.equivariantTilde_obj 𝒜 (gradedModule 𝒜 D)) ≫
    eqToHom (congrArg
      (fun M ↦ (AlgebraicGeometry.tildeEquiv (R := CommRingCat.of A)).functor.obj M)
      (gradedModule_module 𝒜 D)) ≫
    (AlgebraicGeometry.tildeEquiv (R := CommRingCat.of A)).counitIso.hom.app
      (Scheme.QCoh.Equivariant.obj D)

/-- Up to the canonical identification of its source, `counitHom` is the affine tilde counit. -/
theorem counitHom_eq :
    counitHom 𝒜 D =
      eqToHom (GradedSpec.equivariantTilde_obj 𝒜 (gradedModule 𝒜 D)) ≫
        eqToHom (congrArg
          (fun M ↦ (AlgebraicGeometry.tildeEquiv (R := CommRingCat.of A)).functor.obj M)
          (gradedModule_module 𝒜 D)) ≫
        (AlgebraicGeometry.tildeEquiv (R := CommRingCat.of A)).counitIso.hom.app
          (Scheme.QCoh.Equivariant.obj D) := sorry

/-- The affine tilde counit is compatible with the source and target equivariant
linearizations. -/
theorem counitCompatibility :
    Scheme.QCoh.Equivariant.alpha
        (GradedSpec.equivariantTilde 𝒜 (gradedModule 𝒜 D)) ≫
      (Scheme.QCoh.pullback
        (Scheme.QCoh.Equivariant.projection MultiplicativeGroup.group
          (GradedSpec.action 𝒜))).map (counitHom 𝒜 D) =
    (Scheme.QCoh.pullback
      (Scheme.QCoh.Equivariant.action MultiplicativeGroup.group
        (GradedSpec.action 𝒜))).map (counitHom 𝒜 D) ≫
      Scheme.QCoh.Equivariant.alpha D := sorry

/-- The canonical equivariant affine tilde counit for the graded global-sections module. -/
def counit :
    GradedSpec.equivariantTilde 𝒜 (gradedModule 𝒜 D) ⟶ D :=
  Scheme.QCoh.Equivariant.System.Hom.of
    (counitHom 𝒜 D) (CommSq.mk (counitCompatibility 𝒜 D))

/-- The underlying quasi-coherent-module map of `counit` is the affine tilde counit. -/
theorem counit_hom :
    Scheme.QCoh.Equivariant.hom (counit 𝒜 D) = counitHom 𝒜 D := sorry

/-- The canonical equivariant affine tilde counit is an isomorphism. -/
instance counitIsIso : IsIso (counit 𝒜 D) := sorry

end AlgebraicGeometry.GradedSpec.EquivariantSections
