module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic.MultiTwist
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/-
Lemma 33.45.1: for a proper scheme over a field, a coherent module, and a finite family of
invertible modules, the Euler characteristic of every integral multi-twist is a numerical
polynomial whose total degree is at most the dimension of the module's support.
-/
@[stacks 0BEM] #check
  (AlgebraicGeometry.Scheme.Modules.eulerCharacteristic_multiTwist_isMvNumericalPolynomialOfTotalDegreeLE :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (ℱ : X.Modules) [ℱ.IsCoherent]
      {r : ℕ} (L : Fin r → X.Modules)
      [∀ j : Fin r, AlgebraicGeometry.Scheme.Modules.Invertible (L j)],
      IsMvNumericalPolynomialOfTotalDegreeLE
        (fun n ↦ Scheme.Hom.eulerCharacteristic f
          (AlgebraicGeometry.Scheme.Modules.TensorPower.multiTwist ℱ L n))
        (topologicalKrullDim (AlgebraicGeometry.Scheme.Modules.moduleSupport ℱ)))
