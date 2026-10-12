/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Lemma_42_63_3

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.Dedekind

/-- The square formed by a product map over a scheme and the second projections is
cartesian. -/
theorem prodMapSndIsPullback {S : Scheme.{u}} (X : Over S) {Y Z : Over S}
    (g : Y ⟶ Z) :
    IsPullback (Limits.prod.snd : X ⨯ Y ⟶ Y).left
      (Limits.prod.map (𝟙 X) g : X ⨯ Y ⟶ X ⨯ Z).left g.left
      (Limits.prod.snd : X ⨯ Z ⟶ Z).left := sorry

/-- The grading identity relating Dedekind exterior product to a degree-`q` cap. -/
theorem exteriorProductCapDegree (n m q : ℤ) :
    n + (m - q) - 1 = (n + m - 1) - q := sorry

/-- Remark 42.63.4: over a locally Dedekind base, exterior product by a Chow class
commutes with the cap action of a bivariant class. -/
@[stacks 0FC7]
theorem exteriorProduct_cap
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    {X Y Z : Over S} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (g : Y ⟶ Z) (n m q : ℤ)
    (α : RelativeChow δ X n) (c' : BivariantClass δ g q)
    (β : RelativeChow δ Z m) :
    BivariantClass.castRelativeDegree δ (exteriorProductCapDegree n m q)
        (exteriorProductPairing δ h_delta X Y n (m - q) α
          (c'.cap (𝟙 Y) g (𝟙 Z) IsPullback.of_id_fst m β)) =
      c'.cap (Limits.prod.snd : X ⨯ Y ⟶ Y)
        (Limits.prod.map (𝟙 X) g : X ⨯ Y ⟶ X ⨯ Z)
        (Limits.prod.snd : X ⨯ Z ⟶ Z)
        (prodMapSndIsPullback X g) (n + m - 1)
        (exteriorProductPairing δ h_delta X Z n m α β) := sorry

end AlgebraicGeometry.ChowGroup.Dedekind
