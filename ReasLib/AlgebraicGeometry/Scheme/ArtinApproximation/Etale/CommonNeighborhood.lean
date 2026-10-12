/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ArtinApproximation.Etale.Existence

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.ArtinApproximation

/-- A base-compatible equivalence between completed local rings can, to every positive
order, be approximated by a common pointed scheme defining elementary étale
neighborhoods of the two points. -/
theorem exists_commonEtale
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    (s : S) (x : X) (y : Y) (hx : pX x = s) (hy : pY y = s)
    [IsGRing (S.presheaf.stalk s)]
    (φ : AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y) ≃+*
      AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    (hφ_over :
      φ.toRingHom.comp
          ((algebraMap (Y.presheaf.stalk y)
            (AdicCompletion (maximalIdeal (Y.presheaf.stalk y))
              (Y.presheaf.stalk y))).comp (hy ▸ (pY.stalkMap y).hom)) =
        (algebraMap (X.presheaf.stalk x)
          (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x))).comp (hx ▸ (pX.stalkMap x).hom))
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ (U : Scheme.{u}) (u : U) (g : U ⟶ X) (f : U ⟶ Y)
        (hg : Etale g) (hf : Etale f) (hgx : g u = x) (hfy : f u = y)
        (hbase : f ≫ pY = g ≫ pX)
        (hresX : Function.Bijective (IsLocalRing.ResidueField.map (g.stalkMap u).hom))
        (hresY : Function.Bijective (IsLocalRing.ResidueField.map (f.stalkMap u).hom)),
      ∀ a : AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y),
        (hgx ▸ AdicCompletion.mapLocal (g.stalkMap u).hom) (φ a) -
            (hfy ▸ AdicCompletion.mapLocal (f.stalkMap u).hom) a ∈
          AdicCompletion.extendedIdealPow (maximalIdeal (U.presheaf.stalk u)) N := sorry

end AlgebraicGeometry.ArtinApproximation
