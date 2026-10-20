/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Dedekind
public import ReasLib.AlgebraicGeometry.BivariantClass.Commutation

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.Dedekind

/-- Over a locally Dedekind base, the restriction of a bivariant class on `X ⟶ S`
to `X ⨯ Z` commutes with every bivariant class on `Y ⟶ Z`. -/
theorem commute
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    {X Y Z : Over S} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (g : Y ⟶ Z) (p q : ℤ)
    (c : BivariantClass δ (baseMap X) p)
    (c' : BivariantClass δ g q) :
    Commute δ (Limits.prod.snd : X ⨯ Z ⟶ Z) g
      (restrict δ (Limits.prod.fst : X ⨯ Z ⟶ X)
        (Limits.prod.snd : X ⨯ Z ⟶ Z) (baseMap Z)
        (productIsPullback X (baseMap Z)) p c) c' := sorry

end AlgebraicGeometry.BivariantClass.Dedekind
