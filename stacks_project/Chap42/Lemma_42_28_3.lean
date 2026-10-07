module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.Commutativity

@[expose] public section

open CategoryTheory

universe u

/- Lemma 42.28.3: intersection by the first Chern classes of two invertible modules
commutes on relative Chow classes. -/
@[stacks 02TJ]
#check (AlgebraicGeometry.ChowGroup.firstChernClassCap_comm :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [AlgebraicGeometry.LocallyOfFiniteType X.hom]
    (ℒ 𝒩 : X.left.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible ℒ]
    [AlgebraicGeometry.Scheme.Modules.Invertible 𝒩] (k : ℤ)
    (α : AlgebraicGeometry.RelativeChow δ X (k + 2)),
    AlgebraicGeometry.ChowGroup.firstChernClassCap δ X ℒ ((k + 2) - 1)
        (AlgebraicGeometry.ChowGroup.firstChernClassCap δ X 𝒩 (k + 2) α) =
      AlgebraicGeometry.ChowGroup.firstChernClassCap δ X 𝒩 ((k + 2) - 1)
        (AlgebraicGeometry.ChowGroup.firstChernClassCap δ X ℒ (k + 2) α))
