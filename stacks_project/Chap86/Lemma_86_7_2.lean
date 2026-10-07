module

public import stacks_project.Chap86.Lemma_86_7_2_Comparison

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Lemma 86.7.2: in cartesian Tor-independent diagram 86.4.0.1 of algebraic spaces over a
scheme S, for K in DerivedQCoh Y, the square whose horizontal arrows are the maps 86.7.0.1
for K and Lg^* K, whose right vertical arrow is 86.4.1.1, and whose left vertical arrow is
the pullback-tensor/square/structure-sheaf composite, commutes. -/
@[stacks 0E5R]
theorem pullbackTensorDualityMap_baseChange
    {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    [IsIso (modulePullbackDerived.compComparison f' g)]
    [IsIso (modulePullbackDerived.compComparison g' f)]
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g))
    (K : DerivedQCoh Y) :
    let dualIso := dualRightMateIso g' f' f g sq a a' fAdj f'Adj hTor
    CommSq
      ((pullback g').map (pullbackTensorDualityMap f a fAdj K))
      (pullbackTensorDualityBaseChangeMap g' f' f g sq.toCommSq a a' dualIso K)
      (rightAdjointBaseChangeMap g' g a a' dualIso K)
      (pullbackTensorDualityMap f' a' f'Adj ((pullback g).obj K)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
