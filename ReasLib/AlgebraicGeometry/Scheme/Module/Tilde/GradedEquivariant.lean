module

public import ReasLib.Algebra.Module.Graded.Left
public import ReasLib.AlgebraicGeometry.GroupScheme.Action.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.ChangeOfRings.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Spec.GradedAction

/-!
# Equivariant affine tilde modules from integral gradings

This module constructs the extension-of-scalars linearization of an integer-graded module and
transports it to an equivariant quasi-coherent module on the associated affine scheme.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped AlgebraicGeometry ChangeOfRings MonObj MonoidalLeftAction TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GradedSpec

variable {A : Type u} [CommRing A] (𝒜 : ℤ → Submodule ℤ A) [GradedAlgebra 𝒜]

/-- The affine tilde quasicoherent module attached to a graded `A`-module. -/
abbrev affineTilde (M : GradedModule.Left.{0, u, u, 0} 𝒜 ℤ) :
    Scheme.QCoh (Spec (CommRingCat.of A)) :=
  ⟨tilde (@ModuleCat.of A _ M (Module.addCommMonoidToAddCommGroup A) inferInstance),
    inferInstance⟩

/-- The extension-of-scalars linearization attached to an integer-graded module. -/
def linearization (M : GradedModule.Left.{0, u, u, 0} 𝒜 ℤ) :
    (ModuleCat.extendScalars (coactionRingHom 𝒜).hom).obj
        (@ModuleCat.of A _ M (Module.addCommMonoidToAddCommGroup A) inferInstance) ⟶
      (ModuleCat.extendScalars (projectionHom A).hom).obj
        (@ModuleCat.of A _ M (Module.addCommMonoidToAddCommGroup A) inferInstance) :=
  let target : ModuleCat A :=
    (ModuleCat.restrictScalars (coactionRingHom 𝒜).hom).obj
      ((ModuleCat.extendScalars (projectionHom A).hom).obj
        (@ModuleCat.of A _ M (Module.addCommMonoidToAddCommGroup A) inferInstance))
  let adjointHom :
      M →ₗ[A] target :=
    { toFun := fun m ↦
        DirectSum.toAddMonoid
          (fun n ↦
            { toFun := fun x : M.grading n ↦
                ((LaurentPolynomial.T n ⊗ₜ[ULift.{u} ℤ] (1 : A)) :
                  LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] A) ⊗ₜ[A,
                    (projectionHom A).hom] (x : M)
              map_zero' := sorry
              map_add' := sorry })
          (DirectSum.decompose M.grading m)
      map_add' := sorry
      map_smul' := sorry }
  let adjoint :
      @ModuleCat.of A _ M (Module.addCommMonoidToAddCommGroup A) inferInstance ⟶ target :=
    ModuleCat.homEquiv.symm adjointHom
  (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (coactionRingHom 𝒜).hom).symm adjoint

/-- The linearization sends a homogeneous generator to the matching Laurent monomial. -/
theorem linearization_tmul_one_of_mem
    (M : GradedModule.Left.{0, u, u, 0} 𝒜 ℤ)
    (n : ℤ) (m : M) (hm : m ∈ M.grading n) :
    linearization 𝒜 M
        ((1 : LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] A) ⊗ₜ[A,
          (coactionRingHom 𝒜).hom] m) =
      ((LaurentPolynomial.T n ⊗ₜ[ULift.{u} ℤ] (1 : A)) :
        LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] A) ⊗ₜ[A,
          (projectionHom A).hom] m := sorry

/-- After tensor symmetry, the homogeneous formula has the source order
`m ⊗ 1 ⊗ T n`. -/
theorem linearization_sourceFormula
    (M : GradedModule.Left.{0, u, u, 0} 𝒜 ℤ)
    (n : ℤ) (m : M) (hm : m ∈ M.grading n) :
    linearization 𝒜 M
        ((1 : LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] A) ⊗ₜ[A,
          (coactionRingHom 𝒜).hom] m) =
      (Algebra.TensorProduct.comm (ULift.{u} ℤ)
        (LaurentPolynomial (ULift.{u} ℤ)) A).symm
          ((1 : A) ⊗ₜ[ULift.{u} ℤ] LaurentPolynomial.T n) ⊗ₜ[A,
            (projectionHom A).hom] m := sorry

/-- The affine tilde morphism obtained by applying change of rings to `linearization`. -/
def affineLinearization
    (M : GradedModule.Left.{0, u, u, 0} 𝒜 ℤ) :
    (Scheme.QCoh.pullback (Spec.map (coactionRingHom 𝒜))).obj
        (affineTilde 𝒜 M) ⟶
      (Scheme.QCoh.pullback (Spec.map (projectionHom A))).obj
        (affineTilde 𝒜 M) :=
  ObjectProperty.homMk
    ((tilde.ChangeOfRings.Pullback.iso (coactionRingHom 𝒜)).hom.app
        (@ModuleCat.of A _ M (Module.addCommMonoidToAddCommGroup A) inferInstance) ≫
      (tilde.functor
        (CommRingCat.of (LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] A))).map
          (linearization 𝒜 M) ≫
      (tilde.ChangeOfRings.Pullback.iso (projectionHom A)).inv.app
        (@ModuleCat.of A _ M (Module.addCommMonoidToAddCommGroup A) inferInstance))

/-- The underlying module-sheaf map of `affineLinearization` is the change-of-rings
transport of `linearization`. -/
theorem affineLinearization_hom
    (M : GradedModule.Left.{0, u, u, 0} 𝒜 ℤ) :
    (affineLinearization 𝒜 M).hom =
      (tilde.ChangeOfRings.Pullback.iso (coactionRingHom 𝒜)).hom.app
          (@ModuleCat.of A _ M (Module.addCommMonoidToAddCommGroup A) inferInstance) ≫
        (tilde.functor
          (CommRingCat.of (LaurentPolynomial (ULift.{u} ℤ) ⊗[ULift.{u} ℤ] A))).map
            (linearization 𝒜 M) ≫
        (tilde.ChangeOfRings.Pullback.iso (projectionHom A)).inv.app
          (@ModuleCat.of A _ M (Module.addCommMonoidToAddCommGroup A) inferInstance) := sorry

/-- The affine linearization transported from the tensor-product spectrum to the action
product `Gₘ × Spec A`. -/
def tildeLinearization
    (M : GradedModule.Left.{0, u, u, 0} 𝒜 ℤ) :
    (Scheme.QCoh.pullback
      (Scheme.QCoh.Equivariant.action
        MultiplicativeGroup.group (action 𝒜))).obj
          (affineTilde 𝒜 M) ⟶
      (Scheme.QCoh.pullback
        (Scheme.QCoh.Equivariant.projection
          MultiplicativeGroup.group (action 𝒜))).obj
            (affineTilde 𝒜 M) :=
  (GroupoidScheme.pullbackCompIso
      (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).hom
      (Spec.map (coactionRingHom 𝒜))).hom.app
        (affineTilde 𝒜 M) ≫
    (Scheme.QCoh.pullback
      (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).hom).map
        (affineLinearization 𝒜 M) ≫
      (GroupoidScheme.pullbackCompIso
        (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).hom
        (Spec.map (projectionHom A))).inv.app
          (affineTilde 𝒜 M) ≫
        eqToHom (congrArg
          (fun f ↦ (Scheme.QCoh.pullback f).obj
            (affineTilde 𝒜 M))
          (pullbackSpecIso_hom_snd (ULift.{u} ℤ)
            (LaurentPolynomial (ULift.{u} ℤ)) A))

/-- Under the affine change-of-rings comparisons, `tildeLinearization` is induced by the
explicit graded-module map `linearization`. -/
theorem tildeLinearization_affine
    (M : GradedModule.Left.{0, u, u, 0} 𝒜 ℤ) :
    tildeLinearization 𝒜 M =
      (GroupoidScheme.pullbackCompIso
        (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).hom
        (Spec.map (coactionRingHom 𝒜))).hom.app
          (affineTilde 𝒜 M) ≫
        (Scheme.QCoh.pullback
          (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).hom).map
            (affineLinearization 𝒜 M) ≫
          (GroupoidScheme.pullbackCompIso
            (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) A).hom
            (Spec.map (projectionHom A))).inv.app
              (affineTilde 𝒜 M) ≫
            eqToHom (congrArg
              (fun f ↦ (Scheme.QCoh.pullback f).obj
                (affineTilde 𝒜 M))
              (pullbackSpecIso_hom_snd (ULift.{u} ℤ)
                (LaurentPolynomial (ULift.{u} ℤ)) A)) := sorry

/-- The graded affine tilde linearization satisfies the equivariant cocycle law. -/
theorem tildeLinearization_cocycle
    (M : GradedModule.Left.{0, u, u, 0} 𝒜 ℤ) :
    Scheme.QCoh.Equivariant.Cocycle MultiplicativeGroup.group (action 𝒜)
      (affineTilde 𝒜 M)
      (tildeLinearization 𝒜 M) := sorry

/-- The graded affine tilde linearization is the identity along the unit section. -/
theorem tildeLinearization_unit
    (M : GradedModule.Left.{0, u, u, 0} 𝒜 ℤ) :
    Scheme.QCoh.Equivariant.Unit MultiplicativeGroup.group (action 𝒜)
      (affineTilde 𝒜 M)
      (tildeLinearization 𝒜 M) := sorry

/-- The equivariant affine tilde module associated to an integer-graded module. -/
def equivariantTilde
    (M : GradedModule.Left.{0, u, u, 0} 𝒜 ℤ) :
    Scheme.QCoh.Equivariant MultiplicativeGroup.group (action 𝒜) :=
  Scheme.QCoh.Equivariant.of MultiplicativeGroup.group (action 𝒜)
    (affineTilde 𝒜 M)
    (tildeLinearization 𝒜 M) (tildeLinearization_cocycle 𝒜 M)
      (tildeLinearization_unit 𝒜 M)

/-- The quasi-coherent module underlying `equivariantTilde` is the affine tilde of `M`. -/
theorem equivariantTilde_obj
    (M : GradedModule.Left.{0, u, u, 0} 𝒜 ℤ) :
    Scheme.QCoh.Equivariant.obj (equivariantTilde 𝒜 M) =
      affineTilde 𝒜 M := sorry

/-- The linearization stored by `equivariantTilde` is `tildeLinearization`. -/
theorem equivariantTilde_alpha
    (M : GradedModule.Left.{0, u, u, 0} 𝒜 ℤ) :
    Scheme.QCoh.Equivariant.alpha (equivariantTilde 𝒜 M) =
      tildeLinearization 𝒜 M := sorry

end AlgebraicGeometry.GradedSpec
