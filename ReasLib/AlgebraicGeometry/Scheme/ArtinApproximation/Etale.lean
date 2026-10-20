/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood
public import ReasLib.RingTheory.AdicCompletion.Congruence
public import ReasLib.RingTheory.AdicCompletion.LocalMap

@[expose] public section

/-!
# Etale Artin approximations of scheme morphisms

This module bundles an elementary etale neighborhood with a morphism whose
map on the completed local ring agrees with a prescribed formal map to a
specified order.
-/

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- An Artin approximation consists of an elementary etale neighborhood and
a morphism whose induced map on completed local rings has the prescribed
congruence. -/
structure ArtinApproximation
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (x : X) (y : Y)
    (φ : Y.presheaf.stalk y →+*
      AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    (N : ℕ) where
  /-- The elementary etale neighborhood on which the approximation is defined. -/
  neighborhood : Scheme.EtaleNeighborhood.Elementary X x
  /-- The approximating morphism from the neighborhood to `Y`. -/
  toY : neighborhood.obj.toEtale.left ⟶ Y
  /-- The approximating morphism maps the distinguished point to `y`. -/
  toY_point : toY neighborhood.obj.point = y
  /-- The approximating morphism and the neighborhood map have the same composite to `S`. -/
  over_base : toY ≫ pY = neighborhood.obj.toEtale.hom ≫ pX
  /-- The formal and approximating maps agree modulo the `N`-th power of the
  maximal ideal at the distinguished point. -/
  congruent (a : Y.presheaf.stalk y) :
    (neighborhood.obj.map_point ▸
        AdicCompletion.mapLocal
          (neighborhood.obj.toEtale.hom.stalkMap neighborhood.obj.point).hom) (φ a) -
        algebraMap (neighborhood.obj.toEtale.left.presheaf.stalk neighborhood.obj.point)
          (AdicCompletion
            (maximalIdeal
              (neighborhood.obj.toEtale.left.presheaf.stalk neighborhood.obj.point))
            (neighborhood.obj.toEtale.left.presheaf.stalk neighborhood.obj.point))
          ((toY_point ▸ (toY.stalkMap neighborhood.obj.point).hom) a) ∈
      AdicCompletion.extendedIdealPow
        (maximalIdeal
          (neighborhood.obj.toEtale.left.presheaf.stalk neighborhood.obj.point)) N

namespace ArtinApproximation

variable {S X Y : Scheme.{u}} {pX : X ⟶ S} {pY : Y ⟶ S} {x : X} {y : Y}
variable {φ : Y.presheaf.stalk y →+*
  AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)}
variable {N : ℕ}

/-- The scheme underlying the elementary etale neighborhood of an Artin approximation. -/
abbrev source (A : ArtinApproximation pX pY x y φ N) : Scheme.{u} :=
  A.neighborhood.obj.toEtale.left

/-- The distinguished point of the elementary etale neighborhood of an Artin approximation. -/
abbrev point (A : ArtinApproximation pX pY x y φ N) : A.source :=
  A.neighborhood.obj.point

/-- The etale morphism from the neighborhood of an Artin approximation to `X`. -/
abbrev toX (A : ArtinApproximation pX pY x y φ N) : A.source ⟶ X :=
  A.neighborhood.obj.toEtale.hom

/-- Bundle an elementary etale neighborhood and an approximating morphism
satisfying the point, base, and completed-local-ring congruence conditions. -/
def of
    (U : Scheme.EtaleNeighborhood.Elementary X x)
    (f : U.obj.toEtale.left ⟶ Y) (hfy : f U.obj.point = y)
    (hbase : f ≫ pY = U.obj.toEtale.hom ≫ pX)
    (hcongruent : ∀ a : Y.presheaf.stalk y,
      (U.obj.map_point ▸
          AdicCompletion.mapLocal (U.obj.toEtale.hom.stalkMap U.obj.point).hom) (φ a) -
          algebraMap (U.obj.toEtale.left.presheaf.stalk U.obj.point)
            (AdicCompletion (maximalIdeal (U.obj.toEtale.left.presheaf.stalk U.obj.point))
              (U.obj.toEtale.left.presheaf.stalk U.obj.point))
            ((hfy ▸ (f.stalkMap U.obj.point).hom) a) ∈
        AdicCompletion.extendedIdealPow
          (maximalIdeal (U.obj.toEtale.left.presheaf.stalk U.obj.point)) N) :
    ArtinApproximation pX pY x y φ N where
  neighborhood := U
  toY := f
  toY_point := hfy
  over_base := hbase
  congruent := hcongruent

/-- Artin approximation data are inhabited exactly when an elementary etale
neighborhood carries a morphism satisfying the point, base, and congruence conditions. -/
theorem nonempty_iff :
    Nonempty (ArtinApproximation pX pY x y φ N) ↔
      ∃ (U : Scheme.EtaleNeighborhood.Elementary X x)
          (f : U.obj.toEtale.left ⟶ Y) (hfy : f U.obj.point = y)
          (hbase : f ≫ pY = U.obj.toEtale.hom ≫ pX),
        ∀ a : Y.presheaf.stalk y,
          (U.obj.map_point ▸
              AdicCompletion.mapLocal
                (U.obj.toEtale.hom.stalkMap U.obj.point).hom) (φ a) -
              algebraMap (U.obj.toEtale.left.presheaf.stalk U.obj.point)
                (AdicCompletion
                  (maximalIdeal (U.obj.toEtale.left.presheaf.stalk U.obj.point))
                  (U.obj.toEtale.left.presheaf.stalk U.obj.point))
                ((hfy ▸ (f.stalkMap U.obj.point).hom) a) ∈
            AdicCompletion.extendedIdealPow
              (maximalIdeal (U.obj.toEtale.left.presheaf.stalk U.obj.point)) N := sorry

end ArtinApproximation

end AlgebraicGeometry
