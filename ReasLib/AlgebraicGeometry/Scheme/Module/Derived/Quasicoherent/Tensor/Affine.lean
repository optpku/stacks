module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.AffinePullback.Ambient
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Tensor.Right

/-!
# Derived tensor on affine schemes

This module compares derived tensor of affine-associated module complexes with the
affine-associated derived tensor of the original complexes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- On an affine scheme, the derived tensor of the associated module complexes is isomorphic to
the associated module complex of their derived tensor. -/
theorem affineTensor_isomorphic (A : CommRingCat.{u})
    (M K : CochainComplex (ModuleCat A) ℤ) :
    IsIsomorphic
      (tensorObj ((affineFunctor A).obj (Q.obj M))
        ((affineFunctor A).obj (Q.obj K)))
      ((affineFunctor A).obj
        ((DerivedTensor.Right.functor (Q.obj K)).obj (Q.obj M))) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
