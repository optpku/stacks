module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.FourierMukai

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 57.13.5: for a smooth proper scheme over a field, a perfect kernel whose
Fourier–Mukai transform is isomorphic to the identity is isomorphic to the diagonal kernel. -/
@[stacks 0G0E]
#check (AlgebraicGeometry.Scheme.FourierMukai.kernel_iso_diagonal_of_functor_iso_identity :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Smooth X.hom] [IsProper X.hom]
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom X.hom).toRingedSpace),
    Nonempty (AlgebraicGeometry.Scheme.FourierMukai.perfectSelfFunctor X K ≅
      𝟭 (@RingedSpace.ModuleDerived.Perfect X.left.toRingedSpace)) →
    Nonempty (K ≅ AlgebraicGeometry.Scheme.FourierMukai.diagonalKernel X))
