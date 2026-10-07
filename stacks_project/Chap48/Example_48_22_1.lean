module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingModule

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Example 48.22.1: let `A` be a local Noetherian ring, let
`f : X ⟶ Spec (CommRingCat.of A)` be proper. Suppose `ωA` is a normalized dualizing complex
over `A`, `ωS` is its derived affine-tilde complex on `Spec(A)`, and `fShriek` is an exceptional
inverse image satisfying `R(f)_* ⊣ f !`. If `topologicalKrullDim X = d`, then
`H^{-d}(f !ωS)` is the coherent leftmost nonzero cohomology sheaf of a dualizing complex,
and hence is a dualizing module on `X`. -/
@[stacks 0AWI] #check
  (AlgebraicGeometry.Scheme.isDualizingModule_of_proper :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      {X : AlgebraicGeometry.Scheme.{u}}
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [MonoidalCategory
        (AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace)]
      (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (HX : MonoidalClosed
        (AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace))
      (ωA : DerivedCategory (ModuleCat.{u} A))
      (hωA : ωA.IsNormalizedDualizingComplex HA)
      (ωS : AlgebraicGeometry.RingedSpace.ModuleDerived
        (AlgebraicGeometry.Spec (CommRingCat.of A)).toRingedSpace)
      (hωS : IsIsomorphic ωS
        ((AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.affineTildeDerived A).obj ωA))
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) [IsProper f]
      (fShriek : AlgebraicGeometry.Scheme.ExceptionalInverseImage f)
      (d : ℕ) (h_dimension : topologicalKrullDim X = d),
      AlgebraicGeometry.RingedSpace.ModuleDerived.IsDualizingModule
        (fShriek.functor.obj ωS) HX (-(d : ℤ))
        (AlgebraicGeometry.RingedSpace.ModuleDerived.cohomologySheaf
          (fShriek.functor.obj ωS) (-(d : ℤ))))
