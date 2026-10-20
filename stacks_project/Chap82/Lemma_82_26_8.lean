module

import StacksCheckRecall
public import stacks_project.Chap82.Lemma_82_26_8_Commutation

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory
open AlgebraicGeometry.AlgebraicSpace.ChowCohomology

universe u

/- Lemma 82.26.8: In Situation 82.2.1 let `X / B` be good. Let `L` be an
invertible `𝒪_X`-module. Then `c₁(L) ∈ A¹(X)` commutes with every element
`c ∈ Aᵖ(X)`. -/
@[stacks 0ERR] #check
  (AlgebraicGeometry.AlgebraicSpace.ChowCohomology.firstChernClass_comm :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (L : X.Modules) [isInvertibleObject L]
      (p : ℤ) (c : degree δ f p),
      homogeneous δ f 1 (OperationalFirstChern.degree f δ L) * homogeneous δ f p c =
        homogeneous δ f p c * homogeneous δ f 1 (OperationalFirstChern.degree f δ L))
