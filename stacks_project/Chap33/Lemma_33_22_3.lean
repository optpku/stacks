module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.LinearSystem.Dimension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

/- Lemma 33.22.3: over an infinite field, a generating linear system on an algebraic scheme
has a finite-dimensional generating subspace of rank at most the normalized Krull dimension
plus one. -/
@[stacks 0B3Z] #check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.exists_generatingSubmodule_finrank_le_topologicalKrullDim_add_one :
    ∀ {k : Type u} [Field k] [Infinite k]
      (X : Over (Spec (CommRingCat.of k))) [Algebraic X]
      (L : X.left.Modules) [Scheme.Modules.Invertible L]
      {V : Type u} [AddCommGroup V] [Module k V]
      (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L),
      AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.Generates X L ψ →
        ∃ W : Submodule k V,
          FiniteDimensional k W ∧
            (Module.finrank k W : ℕ∞) ≤ (topologicalKrullDim X.left + 1).unbotD 0 ∧
              AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.Generates X L
                (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype ≫ ψ))
