/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SmallToBig.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.TorsorProjection
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Square

/-!
# Derived small-to-big étale direct-image comparisons

The canonical inverse-image squares induce direct-image mates on bounded-below
and unbounded derived categories of abelian sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Adjunction
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open CategoryTheory.Sheaf
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Functor (associator isoWhiskerLeft isoWhiskerRight leftUnitor rightUnitor)
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

variable (f : Y ⟶ X)

/-- Canonical `D⁺` mate `π_X⁻¹ Rf_small,* ⟶ Rf_big,* π_Y⁻¹`. -/
def plusSmallBigPushforwardHom :
    Adjunction.Derived.Plus.right (sheafPushforwardAbelian f) ⋙ FppfEtale.piInverseImagePlus X ⟶
      FppfEtale.piInverseImagePlus Y ⋙
        Adjunction.Derived.Plus.right (bigAbelianPushforward f) :=
  DerivedBaseChange.map
    (Adjunction.Derived.Plus.adjunction (FppfEtale.smallInverseExact f)
      (sheafPushforwardAbelian f) (sheafInverseImageAdjunction f))
    (Adjunction.Derived.Plus.adjunction (etaleTopology.overMapPullbackExact f)
      (bigAbelianPushforward f)
      (etaleTopology.overMapCocontinuousAdjunction AddCommGrpCat.{u + 1} f))
    (FppfEtale.piDerivedSquareIso f)

/-- The bounded-below direct-image comparison is the mate of the canonical inverse-image square. -/
theorem plusSmallBigPushforwardHom_eq :
    plusSmallBigPushforwardHom f =
      DerivedBaseChange.map
        (Adjunction.Derived.Plus.adjunction (FppfEtale.smallInverseExact f)
          (sheafPushforwardAbelian f) (sheafInverseImageAdjunction f))
        (Adjunction.Derived.Plus.adjunction (etaleTopology.overMapPullbackExact f)
          (bigAbelianPushforward f)
          (etaleTopology.overMapCocontinuousAdjunction AddCommGrpCat.{u + 1} f))
        (FppfEtale.piDerivedSquareIso f) := rfl

section UnboundedDerived

variable [IsGrothendieckAbelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [IsGrothendieckAbelian (Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1})]

/-- Inverse-image square on unbounded derived categories. -/
def unboundedSmallBigInverseImageSquare :
    (FppfEtale.etalePiExact X).mapDerivedCategory ⋙
        (etaleTopology.overMapPullbackExact f).mapDerivedCategory ≅
      (FppfEtale.smallInverseExact f).mapDerivedCategory ⋙
        (FppfEtale.etalePiExact Y).mapDerivedCategory :=
  ExactFunctor.MapDerivedCategory.squareIso
    (FppfEtale.etalePiExact X) (etaleTopology.overMapPullbackExact f)
    (FppfEtale.smallInverseExact f) (FppfEtale.etalePiExact Y)
    ((exactFunctor _ _).isoMk (FppfEtale.piInverseImageSquareIso f))

/-- Canonical unbounded derived mate `π_X⁻¹ Rf_small,* ⟶ Rf_big,* π_Y⁻¹`. -/
def unboundedSmallBigPushforwardHom :
    Adjunction.Derived.KInjective.right (sheafPushforwardAbelian f) ⋙
        (FppfEtale.etalePiExact X).mapDerivedCategory ⟶
      (FppfEtale.etalePiExact Y).mapDerivedCategory ⋙
        Adjunction.Derived.KInjective.right (bigAbelianPushforward f) :=
  DerivedBaseChange.map
    (Adjunction.Derived.KInjective.adjunction (FppfEtale.smallInverseExact f)
      (sheafPushforwardAbelian f) (sheafInverseImageAdjunction f))
    (Adjunction.Derived.KInjective.adjunction (etaleTopology.overMapPullbackExact f)
      (bigAbelianPushforward f)
      (etaleTopology.overMapCocontinuousAdjunction AddCommGrpCat.{u + 1} f))
    (unboundedSmallBigInverseImageSquare f)

/-- The unbounded direct-image comparison is the mate of the canonical inverse-image square. -/
theorem unboundedSmallBigPushforwardHom_eq :
    unboundedSmallBigPushforwardHom f =
      DerivedBaseChange.map
        (Adjunction.Derived.KInjective.adjunction (FppfEtale.smallInverseExact f)
          (sheafPushforwardAbelian f) (sheafInverseImageAdjunction f))
        (Adjunction.Derived.KInjective.adjunction (etaleTopology.overMapPullbackExact f)
          (bigAbelianPushforward f)
          (etaleTopology.overMapCocontinuousAdjunction AddCommGrpCat.{u + 1} f))
        (unboundedSmallBigInverseImageSquare f) := rfl

end UnboundedDerived

end AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

end

end
