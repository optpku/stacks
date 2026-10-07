module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Affine
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct

universe u

section

variable {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]

/- Lemma 33.7.5: an affine `k`-scheme is geometrically connected over `k` if and only if
its coordinate algebra remains connected after every field extension of `k`. -/
@[stacks 0386]
#check (AlgebraicGeometry.SchemeOverField.GeometricallyConnected.iff_connectedSpace_primeSpectrum_baseChange :
  AlgebraicGeometry.GeometricallyConnected
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k A))) ↔
    ∀ (K : Type u) [Field K] [Algebra k K],
      ConnectedSpace (PrimeSpectrum (A ⊗[k] K)))

end
