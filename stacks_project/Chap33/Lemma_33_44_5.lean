module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree.Tensor

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry TensorProduct

universe u

/- Lemma 33.44.5: on a proper curve over a field, tensoring a coherent module by a finite
locally free module of rank `n` changes Euler characteristic by the generic fiber rank times the
degree, plus `n` times the original Euler characteristic. -/
@[stacks 0AYV] #check
  (AlgebraicGeometry.Scheme.Modules.eulerCharacteristic_tensor_eq_genericRank_mul_curveDegree_add_rank_mul :
    ∀ {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k))) [Curve X]
      [IsProper X.hom] (ℰ : X.left.Modules) (n : ℕ)
      [Scheme.Modules.IsFiniteLocallyFreeOfRank n ℰ]
      (ℱ : X.left.Modules) [ℱ.IsCoherent],
      let _ : IsLocallyNoetherian X.left :=
        LocallyOfFiniteType.isLocallyNoetherian X.hom
      let _ : ℰ.IsCoherent := Scheme.Modules.isCoherent_of_isFiniteLocallyFreeOfRank n ℰ
      let _ : (ℰ ⊗ ℱ : X.left.Modules).IsCoherent := Scheme.Modules.isCoherent_tensor
      Scheme.Hom.eulerCharacteristic X.hom (ℰ ⊗ ℱ) =
        (Scheme.Modules.fiberFinrank ℱ (genericPoint X.left) : ℤ) *
            Scheme.Modules.curveDegree X.hom
              (AlgebraicGeometry.topologicalKrullDim_eq_one X).le ℰ n +
          (n : ℤ) * Scheme.Hom.eulerCharacteristic X.hom ℱ)
