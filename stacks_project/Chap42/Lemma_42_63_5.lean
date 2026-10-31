/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Dedekind.ExteriorProduct
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 42.63.5: over a locally Dedekind base with dimension function equal to `0`
at closed points and `1` elsewhere, the exterior product on total Chow homology is
associative after pushforward along the canonical associator
`(X ⨯ Y) ⨯ Z ≅ X ⨯ (Y ⨯ Z)`. -/
@[stacks 0FC8] #check
  (AlgebraicGeometry.ChowGroup.Dedekind.exteriorProduct_assoc :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
      [S.HasRingPropertyLocally
        (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (h_delta : ∀ s : S,
        δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
      {X Y Z : Over S}
      [AlgebraicGeometry.LocallyOfFiniteType X.hom]
      [AlgebraicGeometry.LocallyOfFiniteType Y.hom]
      [AlgebraicGeometry.LocallyOfFiniteType Z.hom]
      (α : AlgebraicGeometry.ChowGroup.Total δ X)
      (β : AlgebraicGeometry.ChowGroup.Total δ Y)
      (γ : AlgebraicGeometry.ChowGroup.Total δ Z),
      AlgebraicGeometry.ChowGroup.Total.map δ
          (Limits.prod.associator X Y Z).hom
          (AlgebraicGeometry.ChowGroup.Dedekind.Total.exteriorProduct
            δ h_delta (X ⨯ Y) Z
            (AlgebraicGeometry.ChowGroup.Dedekind.Total.exteriorProduct
              δ h_delta X Y α β) γ) =
        AlgebraicGeometry.ChowGroup.Dedekind.Total.exteriorProduct
          δ h_delta X (Y ⨯ Z) α
          (AlgebraicGeometry.ChowGroup.Dedekind.Total.exteriorProduct
            δ h_delta Y Z β γ))
