/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.ArtinApproximation.Etale
public import ReasLib.RingTheory.Approximation.Artin.Etale.AtPrime.Existence

@[expose] public section

/-!
# Existence of etale Artin approximations of scheme morphisms
-/

open IsLocalRing

universe u

namespace AlgebraicGeometry.ArtinApproximation

/-- A local algebra map from a finite-type stalk to the completed stalk of a
point over a locally Noetherian base with G-ring stalk admits an Artin
approximation to every positive order. -/
theorem nonempty_of_isGRing
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
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
    (N : ℕ) (hN : 1 ≤ N) :
    Nonempty (ArtinApproximation pX pY x y φ N) := sorry

end AlgebraicGeometry.ArtinApproximation
