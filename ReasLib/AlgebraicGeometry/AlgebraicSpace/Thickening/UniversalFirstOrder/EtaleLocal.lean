module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.Functorial
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyUnramified.EtaleLocal

/-!
# Étale localization of universal first-order thickenings

The canonical comparison of universal first-order thickenings associated to an
étale localization square is étale, its closed-subspace square is cartesian,
and its induced conormal map is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

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
