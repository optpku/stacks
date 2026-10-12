/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap76.Lemma_76_15_8_Comparison

/-!
# Étale localization of universal first-order thickenings

A commutative square of algebraic spaces with étale vertical arrows preserves
formal unramifiedness of the bottom arrow, and the canonical comparison of
universal first-order thickenings is an étale cartesian morphism whose induced
conormal map is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FormallyUnramified

/-- On a commutative square of algebraic spaces with étale vertical arrows, the
top arrow is formally unramified as soon as the bottom arrow is. -/
theorem of_etaleCommSq {S : Scheme.{u}} {X Z U V : AlgebraicSpace S}
    (fVU : V ⟶ U) (fVZ : V ⟶ Z) (fUX : U ⟶ X) (h : Z ⟶ X)
    [FormallyUnramified h] [Etale fVZ] [Etale fUX]
    (sq : CommSq fVU fVZ fUX h) : FormallyUnramified fVU :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FormallyUnramified

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder

/-- The canonical comparison of universal first-order thickenings associated to
an étale localization square is étale. -/
instance comparison_etale {S : Scheme.{u}} {X Z U V Z' V' : AlgebraicSpace S}
    (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iV : V ⟶ V') (fV : V' ⟶ U)
    (fVZ : V ⟶ Z) (fUX : U ⟶ X)
    [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iV fV]
    [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iV ≫ fV)]
    [Etale fVZ] [Etale fUX]
    (sq : CommSq fVZ (iV ≫ fV) (iZ ≫ fZ) fUX) :
    Etale (comparison iV fV iZ fZ fVZ fUX sq) :=
  sorry

/-- The closed-subspace square of the canonical étale comparison of universal
first-order thickenings is cartesian. -/
theorem comparison_isPullback {S : Scheme.{u}}
    {X Z U V Z' V' : AlgebraicSpace S}
    (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iV : V ⟶ V') (fV : V' ⟶ U)
    (fVZ : V ⟶ Z) (fUX : U ⟶ X)
    [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iV fV]
    [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iV ≫ fV)]
    [Etale fVZ] [Etale fUX]
    (sq : CommSq fVZ (iV ≫ fV) (iZ ≫ fZ) fUX) :
    IsPullback iV fVZ (comparison iV fV iZ fZ fVZ fUX sq) iZ :=
  sorry

/-- The canonical comparison of conormal sheaves associated to an étale
localization square of universal first-order thickenings is an isomorphism. -/
instance conormalMap_isIso_of_etale {S : Scheme.{u}}
    {X Z U V Z' V' : AlgebraicSpace S}
    (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iV : V ⟶ V') (fV : V' ⟶ U)
    (fVZ : V ⟶ Z) (fUX : U ⟶ X)
    [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iV fV]
    [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iV ≫ fV)]
    [Etale fVZ] [Etale fUX]
    (sq : CommSq fVZ (iV ≫ fV) (iZ ≫ fZ) fUX) :
    IsIso (conormalMap iV fV iZ fZ fVZ fUX sq) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
