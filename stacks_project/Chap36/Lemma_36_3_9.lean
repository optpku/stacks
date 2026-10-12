/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Tensor.Affine

@[expose] public section

noncomputable section

universe u

/- Lemma 36.3.9 (1): the derived tensor product of two objects of `D_QCoh(𝒪_X)`
again has quasicoherent cohomology. -/
@[stacks 08DX] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.tensorRight.mapsTo :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}
      (L : CategoryTheory.DerivedCategory.CohomologyIn
        (AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)),
      CategoryTheory.DerivedCategory.cohomologyIn
          (AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ≤
        (CategoryTheory.DerivedCategory.cohomologyIn
          (AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty
            X.toRingedSpace)).inverseImage
            (CategoryTheory.DerivedCategory.DerivedTensor.Right.functor L.obj))

/- Lemma 36.3.9 (2): on `Spec A`, the derived tensor product of the affine-associated
complexes of `M` and `K` is isomorphic to the affine-associated complex of `M ⊗ᴸ_A K`. -/
@[stacks 08DX] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.affineTensor_isomorphic :
    ∀ (A : CommRingCat.{u}) (M K : CochainComplex (ModuleCat A) ℤ),
      CategoryTheory.IsIsomorphic
        (AlgebraicGeometry.Scheme.DerivedQCoh.tensorObj
          ((AlgebraicGeometry.Scheme.DerivedQCoh.affineFunctor A).obj
            (DerivedCategory.Q.obj M))
          ((AlgebraicGeometry.Scheme.DerivedQCoh.affineFunctor A).obj
            (DerivedCategory.Q.obj K)))
        ((AlgebraicGeometry.Scheme.DerivedQCoh.affineFunctor A).obj
          ((CategoryTheory.DerivedCategory.DerivedTensor.Right.functor
            (DerivedCategory.Q.obj K)).obj
              (DerivedCategory.Q.obj M))))
