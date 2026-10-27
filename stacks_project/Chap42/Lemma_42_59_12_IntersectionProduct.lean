/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Intersection

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChowGroup AlgebraicGeometry.Scheme.VectorBundleK0
open AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
open scoped BigOperators DirectSum TensorProduct Topology

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

#check (AlgebraicGeometry.ChowGroup.chernCapFundamental :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    [CompactSpace X.left] (classes : ChernClass.Theory δ X.hom)
    (hdim : topologicalKrullDim X.left < ⊤),
    TensorProduct ℤ (Scheme.VectorBundleK0 X.left) ℚ →+ rationalChow δ X)

end AlgebraicGeometry.ChowGroup

namespace AlgebraicGeometry.ChowGroup

#check (AlgebraicGeometry.ChowGroup.rationalIntersectionProduct :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    [CompactSpace X.left] (classes : ChernClass.Theory δ X.hom)
    (hdim : topologicalKrullDim X.left < ⊤)
    (α β : TensorProduct ℤ (Scheme.VectorBundleK0 X.left) ℚ),
    rationalChow δ X)

end AlgebraicGeometry.ChowGroup

namespace AlgebraicGeometry.Scheme.VectorBundleK0

#check (AlgebraicGeometry.Scheme.VectorBundleK0.pullbackRational :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    TensorProduct ℤ (VectorBundleK0 Y) ℚ →+ TensorProduct ℤ (VectorBundleK0 X) ℚ)

end AlgebraicGeometry.Scheme.VectorBundleK0

namespace AlgebraicGeometry.BivariantClass

#check (AlgebraicGeometry.BivariantClass.gysinMap :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ)
    [IsDimensionFunction δ] {X Y : Over S} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f.left] {P : Over S}
    [LocallyOfFiniteType P.hom] (ι : X ⟶ P) (σ : P ⟶ Y) (hι : IsImmersion ι.left)
    [IsClosedImmersion ι.left] [IsRegularImmersion ι.left] [hσ : Smooth σ.left]
    (hfac : ι ≫ σ = f) (t : ℕ) [Scheme.Hom.RelativeDimension σ.left t] (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf ι.left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf ι.left) ≅
      Scheme.Hom.conormalSheaf ι.left)
    (D : ClosedDeformation X.hom P.hom ι.left (Over.w ι)
      (ofNormalSheaf ι.left r e)),
    rationalChow δ Y →+ rationalChow δ X)

end AlgebraicGeometry.BivariantClass

