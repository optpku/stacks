/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Lemma_42_64_1_IntersectionProduct
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 42.64.1: over a locally Dedekind base with dimension function equal to `0`
at closed points and `1` elsewhere, if `X` is smooth over `S` and `Y`, `Z`, `W` are
locally of finite type over `X`, the intersection product on total Chow homology is
associative after pushforward along the canonical fiber-product associator
`(Y ×_X Z) ×_X W ≅ Y ×_X (Z ×_X W)`. -/
@[stacks 0FCA] #check
  (AlgebraicGeometry.ChowGroup.Dedekind.intersectionProduct_assoc :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
      [S.HasRingPropertyLocally
        (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (h_delta : ∀ s : S,
        δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
      {X Y Z W : Over S}
      [AlgebraicGeometry.LocallyOfFiniteType X.hom]
      [AlgebraicGeometry.Smooth X.hom]
      [AlgebraicGeometry.LocallyOfFiniteType Y.hom]
      [AlgebraicGeometry.LocallyOfFiniteType Z.hom]
      [AlgebraicGeometry.LocallyOfFiniteType W.hom]
      (fY : Y ⟶ X) (fZ : Z ⟶ X) (fW : W ⟶ X)
      [AlgebraicGeometry.LocallyOfFiniteType fY.left]
      [AlgebraicGeometry.LocallyOfFiniteType fZ.left]
      [AlgebraicGeometry.LocallyOfFiniteType fW.left]
      (e : AlgebraicGeometry.Scheme.Modules.dual
        (AlgebraicGeometry.Scheme.Hom.normalSheaf
          (AlgebraicGeometry.ChowGroup.Dedekind.diagonal X).left) ≅
        AlgebraicGeometry.Scheme.Hom.conormalSheaf
          (AlgebraicGeometry.ChowGroup.Dedekind.diagonal X).left)
      (D : AlgebraicGeometry.ChowGroup.Dedekind.DiagonalSpecialization δ X e)
      (r : ℕ)
      [AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank r
        (AlgebraicGeometry.Scheme.Hom.conormalSheaf
          (AlgebraicGeometry.ChowGroup.Dedekind.diagonal X).left)]
      (α : AlgebraicGeometry.ChowGroup.Dedekind.Total δ Y)
      (β : AlgebraicGeometry.ChowGroup.Dedekind.Total δ Z)
      (γ : AlgebraicGeometry.ChowGroup.Dedekind.Total δ W),
      AlgebraicGeometry.ChowGroup.Dedekind.Total.map δ
          (AlgebraicGeometry.ChowGroup.Dedekind.fiberProductAssociator
            fY fZ fW).hom
          (AlgebraicGeometry.ChowGroup.Dedekind.intersectionProduct
            δ h_delta
            (AlgebraicGeometry.ChowGroup.Dedekind.fiberProductToBase fY fZ) fW
            e D r
            (AlgebraicGeometry.ChowGroup.Dedekind.intersectionProduct
              δ h_delta fY fZ e D r α β) γ) =
        AlgebraicGeometry.ChowGroup.Dedekind.intersectionProduct
          δ h_delta fY
          (AlgebraicGeometry.ChowGroup.Dedekind.fiberProductToBase fZ fW)
          e D r α
          (AlgebraicGeometry.ChowGroup.Dedekind.intersectionProduct
            δ h_delta fZ fW e D r β γ))
