module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Affine
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Category
public import ReasLib.RingTheory.Ideal.AssociatedGraded.AdicFinite

/-!
# Associated graded modules of coherent formal modules

This file records the affine-local associated graded description and finite-generation property
of the transition kernels in a coherent formal module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

namespace TransitionKernelDirectSum

/-- The transition kernels of a coherent formal module form a finite-type associated graded
module when they are quasi-coherent, identify on each affine open with the successive adic
quotients of a finite completed module, and their canonical associated graded module is finite. -/
def IsFiniteType
    {X : Scheme.{u}} (I : X.IdealSheafData) (F : CoherentFormalModules X I) : Prop :=
  (∀ n : ℕ, (kernel (F.obj.stepMap n).hom).IsQuasicoherent) ∧
    ∀ U : X.affineOpens,
      ∃ (M : Type u) (_ : AddCommGroup M)
        (_ : Module (AdicCompletion (I.ideal U) Γ(X, U.1)) M)
        (_ : Module Γ(X, U.1) M)
        (_ : IsScalarTower Γ(X, U.1) (AdicCompletion (I.ideal U) Γ(X, U.1)) M)
        (_ : Module.Finite (AdicCompletion (I.ideal U) Γ(X, U.1)) M),
        ∃ _ : ∀ n : ℕ,
          (kernel (F.obj.stepMap n).hom).val.obj (op U.1) ≃ₗ[Γ(X, U.1)]
            Ideal.AssociatedGraded.piece (I.ideal U) M n,
          Module.Finite (Ideal.AssociatedGraded.ring (I.ideal U))
            (Ideal.AssociatedGraded.gradedModule (I.ideal U) M)

end TransitionKernelDirectSum

/-- On a Noetherian scheme, the transition kernels of a coherent formal module form a
finite-type graded quasi-coherent module over the associated graded ideal algebra. -/
theorem transitionKernelDirectSum_finite
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (F : CoherentFormalModules X I) :
    TransitionKernelDirectSum.IsFiniteType I F := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
