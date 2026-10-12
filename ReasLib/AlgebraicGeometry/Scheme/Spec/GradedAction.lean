/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import ReasLib.AlgebraicGeometry.MultiplicativeGroup

/-!
# The multiplicative-group action attached to an integral grading

This module constructs the Laurent coaction of an integer-graded commutative ring and the
corresponding action of the integral multiplicative group on its affine spectrum.
-/

@[expose] public section

namespace AlgebraicGeometry

attribute [scoped instance] ULift.algebra'

end AlgebraicGeometry

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped AlgebraicGeometry MonObj MonoidalLeftAction TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GradedSpec

variable {A : Type u} [CommRing A] (𝒜 : ℤ → Submodule ℤ A) [GradedAlgebra 𝒜]

/-- The Laurent coaction associated to the grading, with the Laurent factor first. -/
def coaction :
    A →ₐ[ULift.{u} ℤ] LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] A :=
  { (DirectSum.toSemiring
      (fun n ↦
        { toFun := fun f : 𝒜 n ↦ LaurentPolynomial.T n ⊗ₜ[ULift.{u} ℤ] (f : A)
          map_zero' := sorry
          map_add' := sorry })
      sorry sorry).comp (DirectSum.decomposeRingEquiv 𝒜).toRingHom with
    commutes' := sorry }

/-- On an element homogeneous of degree `n`, `coaction` adjoins the Laurent monomial `T n`. -/
theorem coaction_apply_of_mem (n : ℤ) (f : A) (hf : f ∈ 𝒜 n) :
    coaction 𝒜 f = LaurentPolynomial.T n ⊗ₜ[ULift.{u} ℤ] f := sorry

/-- In the source tensor order, a homogeneous `f` is sent to `f ⊗ₜ T n`. -/
theorem coaction_sourceFormula (n : ℤ) (f : A) (hf : f ∈ 𝒜 n) :
    Algebra.TensorProduct.comm (ULift.{u} ℤ)
        (LaurentPolynomial (ULift.{u} ℤ)) A (coaction 𝒜 f) =
      f ⊗ₜ[ULift.{u} ℤ] LaurentPolynomial.T n := sorry

/-- The Laurent coaction as a morphism of commutative-ring objects, with the canonical
`CommRing` instance on its tensor-product codomain. -/
def coactionRingHom : CommRingCat.of A ⟶
    CommRingCat.of (LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] A) :=
  CommRingCat.ofHom (coaction 𝒜).toRingHom

/-- The commutative-ring bridge for `coaction` has the same underlying function. -/
theorem coactionRingHom_apply (f : A) : coactionRingHom 𝒜 f = coaction 𝒜 f := sorry

/-- The Laurent coaction is counital. -/
theorem coaction_counit :
    (Algebra.TensorProduct.lid (ULift.{u} ℤ) A).toAlgHom.comp
      ((Algebra.TensorProduct.map
        (Bialgebra.counitAlgHom (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)))
        (AlgHom.id (ULift.{u} ℤ) A)).comp (coaction 𝒜)) =
      AlgHom.id (ULift.{u} ℤ) A := sorry

/-- The Laurent coaction is coassociative. -/
theorem coaction_coassoc :
    (TensorProduct.assoc (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ))
      (LaurentPolynomial (ULift.{u} ℤ)) A).toLinearMap.comp
        ((TensorProduct.map
          (Bialgebra.comulAlgHom
            (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ))).toLinearMap
          (LinearMap.id : A →ₗ[ULift.{u} ℤ] A)).comp (coaction 𝒜).toLinearMap) =
      (TensorProduct.map
        (LinearMap.id : LaurentPolynomial (ULift.{u} ℤ) →ₗ[ULift.{u} ℤ]
          LaurentPolynomial (ULift.{u} ℤ))
        (coaction 𝒜).toLinearMap).comp (coaction 𝒜).toLinearMap := sorry

/-- The coordinate-ring map of the projection from `Gₘ × Spec A` to `Spec A`. -/
def projectionRingHom (A : Type u) [CommRing A] :
    A →+* LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] A :=
  (Algebra.TensorProduct.includeRight :
    A →ₐ[ULift.{u} ℤ] LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] A).toRingHom

/-- The projection coordinate map sends `f` to `1 ⊗ₜ f`. -/
theorem projectionRingHom_apply (f : A) :
    projectionRingHom A f =
      (1 : LaurentPolynomial (ULift.{u} ℤ)) ⊗ₜ[ULift.{u} ℤ] f := sorry

/-- The projection coordinate map as a morphism of commutative-ring objects. -/
def projectionHom (A : Type u) [CommRing A] : CommRingCat.of A ⟶
    CommRingCat.of (LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] A) :=
  CommRingCat.ofHom (projectionRingHom A)

/-- The commutative-ring bridge for the projection has the expected value. -/
theorem projectionHom_apply (f : A) :
    projectionHom A f =
      (1 : LaurentPolynomial (ULift.{u} ℤ)) ⊗ₜ[ULift.{u} ℤ] f := sorry

/-- The grading coaction induces a morphism from `Gₘ × Spec A` to `Spec A`. -/
def actionHom :
    MultiplicativeGroup.overInt ⊗
        Scheme.OverSpec.affine (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) A)) ⟶
      Scheme.OverSpec.affine (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) A)) :=
  Over.homMk
    ((pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).hom ≫
      Spec.map (coactionRingHom 𝒜)) sorry

/-- The underlying scheme map of `actionHom` is induced by `coaction`. -/
theorem actionHom_left :
    (actionHom 𝒜).left =
      (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).hom ≫
        Spec.map (coactionRingHom 𝒜) := sorry

/-- The grading action satisfies the identity-action law. -/
theorem actionHom_one_smul :
    η[MultiplicativeGroup.overInt] ⊵ₗ
          Scheme.OverSpec.affine (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) A)) ≫
        actionHom 𝒜 =
      (λₗ (Scheme.OverSpec.affine
        (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) A)))).hom := sorry

/-- The grading action is compatible with multiplication in `Gₘ`. -/
theorem actionHom_mul_smul :
    μ[MultiplicativeGroup.overInt] ⊵ₗ
          Scheme.OverSpec.affine (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) A)) ≫
        actionHom 𝒜 =
      (αₗ MultiplicativeGroup.overInt MultiplicativeGroup.overInt
        (Scheme.OverSpec.affine
          (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) A)))).hom ≫
        MultiplicativeGroup.overInt ⊴ₗ actionHom 𝒜 ≫ actionHom 𝒜 := sorry

/-- The module-object structure on the canonical affine object `Spec A` over
`Spec (ULift ℤ)` induced by its grading. -/
@[reducible]
def actionModObj :
    ModObj MultiplicativeGroup.overInt
      (Scheme.OverSpec.affine (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) A))) where
  smul := actionHom 𝒜
  one_smul := actionHom_one_smul 𝒜
  mul_smul := actionHom_mul_smul 𝒜

/-- The action stored in `actionModObj` is the morphism induced by the Laurent coaction. -/
theorem actionModObj_smul : (actionModObj 𝒜).smul = actionHom 𝒜 := sorry

/-- The action of the integral multiplicative group on `Spec A` associated to the grading. -/
def action : Mod (Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    MultiplicativeGroup.group.X where
  X := Scheme.OverSpec.affine (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) A))
  mod := actionModObj 𝒜

/-- The object underlying the graded affine action is the canonical affine `Spec A` over
`Spec (ULift ℤ)`. -/
theorem action_X :
    (action 𝒜).X =
      Scheme.OverSpec.affine (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) A)) := sorry

/-- The stored action morphism is the map induced by `coaction`. -/
theorem action_smul : (action 𝒜).mod.smul = actionHom 𝒜 := sorry

end AlgebraicGeometry.GradedSpec
