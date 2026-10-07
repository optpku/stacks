module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.RationalPoint

@[expose] public section

open CategoryTheory Limits
open scoped MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.FieldExtension

universe u

/- Lemma 45.8.3: for two rational points on a geometrically irreducible smooth
projective scheme over `k`, their degree-zero Chow-class difference becomes divisible
by an integer `n` after some finite separable extension of `k`, provided `n` is
invertible in `k`. -/
@[stacks 0FH7]
#check (AlgebraicGeometry.ChowGroup.rationalPointSub_divisible :
  ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
    [GeometricallyIrreducible X.hom] [AlgebraicGeometry.Smooth X.hom]
    [AlgebraicGeometry.Projective X.hom]
    (x x' : 𝟙_ (AlgebraicGeometry.SchemeOverField k) ⟶ X) (n : ℤ) (hn : IsUnit (n : k)),
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : FiniteDimensional k K)
      (_ : Algebra.IsSeparable k K)
      (z : @AlgebraicGeometry.ChowGroup (pullback X.hom (specMap k K))
        (@AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
          (pullback X.hom (specMap k K)) (Spec (CommRingCat.of K))
          (pullback.snd X.hom (specMap k K)) inferInstance
          (@AlgebraicGeometry.instUniversallyCatenarySpec K _
            (@instUniversallyCatenaryRingOfField.{u, u} K _)).toIsLocallyNoetherian)
        ((pullback.snd X.hom (specMap k K)).relativeDimensionFunction
          (fun _ : Spec (CommRingCat.of K) ↦ (0 : ℤ)))
        (@AlgebraicGeometry.Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction
          (pullback X.hom (specMap k K)) (Spec (CommRingCat.of K))
          (pullback.snd X.hom (specMap k K))
          (@AlgebraicGeometry.instUniversallyCatenarySpec K _
            (@instUniversallyCatenaryRingOfField.{u, u} K _))
          inferInstance (fun _ : Spec (CommRingCat.of K) ↦ (0 : ℤ))
          (@instIsDimensionFunctionZero (Spec (CommRingCat.of K)) inferInstance inferInstance)) 0),
      AlgebraicGeometry.ChowGroup.FieldExtension.algebraicExtensionPullback k K X 0
          (AlgebraicGeometry.ChowGroup.rationalPointClass X x -
            AlgebraicGeometry.ChowGroup.rationalPointClass X x') = n • z)
