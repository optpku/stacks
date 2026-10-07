module

public import ReasLib.AlgebraicGeometry.Scheme.ArtinApproximation.Etale.Existence
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

/- Lemma 37.39.1: let `S` be locally Noetherian, let `X` and `Y` be locally of
finite type over `S`, and let `x : X` and `y : Y` lie over `s : S`.  If
`𝒪_{S,s}` is a G-ring, then every local `𝒪_{S,s}`-algebra map from `𝒪_{Y,y}`
to the completed local ring at `x` admits, to every positive order, an
approximation on an elementary etale neighborhood of `(X, x)`. -/
@[stacks 0CAU]
#check (AlgebraicGeometry.ArtinApproximation.nonempty_of_isGRing :
  ∀ {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    (s : S) (x : X) (y : Y) (hx : pX x = s) (hy : pY y = s)
    [IsGRing (S.presheaf.stalk s)]
    (φ : Y.presheaf.stalk y →+*
      AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    [IsLocalHom φ]
    (hφ_over :
      φ.comp (hy ▸ (pY.stalkMap y).hom) =
        (algebraMap (X.presheaf.stalk x)
          (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x))).comp (hx ▸ (pX.stalkMap x).hom))
    (N : ℕ) (hN : 1 ≤ N),
    Nonempty (ArtinApproximation pX pY x y φ N))
