/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.ObstructionTheory
public import ReasLib.RingTheory.Extension.Cotangent.Obstruction.Derived

/-! # Obstruction theory of an affine polynomial quotient -/

@[expose] public section

set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry GroupoidsOver
noncomputable section
universe u

namespace AlgebraicGeometry.Deformation.PresentedAlgebra

variable {Λ ι : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable (J : Ideal (MvPolynomial ι Λ))

/-- The slice represented by the spectrum of a polynomial quotient over the base spectrum. -/
abbrev presentedSlice : GroupoidsOver (Spec (CommRingCat.of Λ)) :=
  GroupoidsOver.slice
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ (MvPolynomial ι Λ ⧸ J)))))

/-- The coefficient algebra of an affine object, recovered from its structure morphism. -/
def coefficients (ξ : ObjectOverSpec (presentedSlice J)) : CommAlgCat Λ :=
  @CommAlgCat.of Λ _ ξ.carrier inferInstance (Spec.preimage ξ.toS).hom.toAlgebra

/-- The coefficient algebra of the source of a square-zero deformation. -/
private def sourceCoefficients (σ : DeformationSituation (presentedSlice J)) : CommAlgCat Λ :=
  @CommAlgCat.of Λ _ σ.source inferInstance (Spec.preimage σ.sourceToS).hom.toAlgebra

/-- The algebra map of an affine object of the represented slice. -/
def objectAlgHom (ξ : ObjectOverSpec (presentedSlice J)) :
    (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] coefficients J ξ where
  __ := (Spec.preimage
    (eqToHom (congrArg (fun T : Over (Spec (CommRingCat.of Λ)) => T.left)
      ξ.over_obj).symm ≫ ξ.obj.hom.left)).hom
  commutes' := sorry

/-- The algebra homomorphism of the stored square-zero extension. -/
private abbrev extensionAlgHom (σ : DeformationSituation (presentedSlice J)) :
    sourceCoefficients J σ →ₐ[Λ] coefficients J σ.toObjectOverSpec where
  __ := σ.toCarrier
  commutes' := sorry

/-- The coefficient algebra homomorphism of a morphism of obstruction triples. -/
private def tripleAlgHom {ξ η : ObstructionTriple (presentedSlice J)}
    (f : ObstructionTriple.Hom ξ η) :
    coefficients J ξ.toObjectOverSpec →ₐ[Λ] coefficients J η.toObjectOverSpec where
  __ := f.toRingHom
  commutes' := sorry

/-- Geometric lifts of an affine slice object are precisely lifts of its algebra map. -/
private theorem objectLift_iff_hasLift (σ : DeformationSituation (presentedSlice J)) :
    Nonempty (DeformationSituation.ObjectLift σ) ↔
      AlgHom.HasLift (extensionAlgHom J σ) (objectAlgHom J σ.toObjectOverSpec) :=
  sorry

/-- The cotangent Hom cokernel and polynomial-evaluation class form an obstruction theory
for the slice represented by an affine polynomial quotient. -/
def theory : GroupoidsOver.ObstructionTheory (presentedSlice J) where
  module ξ := Algebra.NaiveCotangent.Obstruction.functor
    (A := coefficients J ξ) J (objectAlgHom J ξ)
  moduleLinear ξ := Algebra.NaiveCotangent.Obstruction.functorModuleLinear
    (A := coefficients J ξ) J (objectAlgHom J ξ)
  map {ξ η} f := ConcreteCategory.ofHom
    (Algebra.NaiveCotangent.Obstruction.coefficientMap J
      (objectAlgHom J ξ.toObjectOverSpec) (objectAlgHom J η.toObjectOverSpec)
      (tripleAlgHom J f) sorry
      (N := ξ.M) (N' := η.M)
      { toFun := f.toModule
        map_add' := f.toModule.hom.map_add
        map_smul' := f.toModule.hom.map_smul })
  obstruction σ :=
    Algebra.NaiveCotangent.Obstruction.coefficientMap J
      (objectAlgHom J σ.toObjectOverSpec) (objectAlgHom J σ.toObjectOverSpec)
      (AlgHom.id Λ (coefficients J σ.toObjectOverSpec)) (by ext; rfl)
      (N := ModuleCat.of (coefficients J σ.toObjectOverSpec)
        (RingHom.SquareZeroExtension.KernelModule (extensionAlgHom J σ).toRingHom))
      (N' := σ.kernelModule) σ.kernelModuleComparison.toLinearMap
      (Algebra.NaiveCotangent.Obstruction.obstruction
        (extensionAlgHom J σ) J (objectAlgHom J σ.toObjectOverSpec))
  map_id := sorry
  map_comp := sorry
  map_module := sorry
  map_obstruction := sorry
  lifts_iff := sorry

/-- The module functor of the affine obstruction theory is the cotangent Hom cokernel. -/
theorem theory_module (ξ : ObjectOverSpec (presentedSlice J)) :
    (theory J).module ξ = Algebra.NaiveCotangent.Obstruction.functor
      (A := coefficients J ξ) J (objectAlgHom J ξ) :=
  rfl

/-- The affine obstruction element is the polynomial-evaluation class transported by
the identity comparison of kernel modules. -/
theorem theory_obstruction (σ : DeformationSituation (presentedSlice J)) :
    (theory J).obstruction σ =
      Algebra.NaiveCotangent.Obstruction.coefficientMap J
        (objectAlgHom J σ.toObjectOverSpec) (objectAlgHom J σ.toObjectOverSpec)
        (AlgHom.id Λ (coefficients J σ.toObjectOverSpec)) (by ext; rfl)
        (N := ModuleCat.of (coefficients J σ.toObjectOverSpec)
          (RingHom.SquareZeroExtension.KernelModule (extensionAlgHom J σ).toRingHom))
        (N' := σ.kernelModule) σ.kernelModuleComparison.toLinearMap
        (Algebra.NaiveCotangent.Obstruction.obstruction
          (extensionAlgHom J σ) J (objectAlgHom J σ.toObjectOverSpec)) :=
  sorry

end AlgebraicGeometry.Deformation.PresentedAlgebra
