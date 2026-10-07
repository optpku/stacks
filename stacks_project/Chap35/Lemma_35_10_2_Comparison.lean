module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Counterexample

/-!
# Associated-module comparison compatibility bridge

The comparison API formerly exposed from this module is owned by the reusable
associated-module library modules imported above.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry

noncomputable section

universe u

#check
  (AlgebraicGeometry.Scheme.AssociatedModule.bigModuleTensorComparison :
    (S : Scheme.{u}) → (τ : StandardTopology) → (F G : Scheme.QCoh S) →
      (AlgebraicGeometry.Scheme.AssociatedModule.bigModuleLift S τ).obj
          ((AlgebraicGeometry.Scheme.AssociatedModule.bigModuleFunctor S τ).obj F) ⊗
          (AlgebraicGeometry.Scheme.AssociatedModule.bigModuleLift S τ).obj
            ((AlgebraicGeometry.Scheme.AssociatedModule.bigModuleFunctor S τ).obj G) ⟶
        (AlgebraicGeometry.Scheme.AssociatedModule.bigModuleLift S τ).obj
          ((AlgebraicGeometry.Scheme.AssociatedModule.bigModuleFunctor S τ).obj
            (AlgebraicGeometry.Scheme.AssociatedModule.quasicoherentTensor S F G)))
