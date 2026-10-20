/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.AbelianComparison
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Square
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Consequences

/-!
# Bounded-below derived small-étale to ph comparison

Exact inverse-image squares induce bounded-below derived inverse images and their
canonical direct-image mate. The comparison unit and the proper direct-image mate are
isomorphisms for complexes with locally torsion cohomology sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Adjunction.Derived
open CategoryTheory.ExactFunctor.Derived.Plus (squareIso)
open CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale.SmallToBig

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PhComparison

/-- Exact inverse image `π_X⁻¹` on abelian small-étale sheaves. -/
abbrev piExact {S : Scheme.{u}} (X : Over S) :
    Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ₑ
      Sheaf ((S.overGrothendieckTopology @Etale).over X) AddCommGrpCat.{u + 1} :=
  ExactFunctor.of (piInverseImage X)

/-- Exact inverse image along small étale base change. -/
abbrev smallPullbackExact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ₑ
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  ExactFunctor.of (smallPullbackAb f)

/-- Bundled exact-functor form of the abelian small-étale inverse-image square. -/
def abelianSmallEtaleExactSquare {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    (piExact Y).comp
        ((S.overGrothendieckTopology @Etale).overMapPullbackExact f) ≅
      (smallPullbackExact f.left).comp (piExact X) :=
  (exactFunctor
      (Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u + 1})
      (Sheaf ((S.overGrothendieckTopology @Etale).over X)
        AddCommGrpCat.{u + 1})).isoMk
    (abelianSmallEtaleInverseImageSquare f)

/-- Bundled exact-functor form of the abelian small-to-ph inverse-image square. -/
def abelianSmallPhExactSquare {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    (ExactFunctor.of (aInverseImage Y)).comp
        ((Scheme.bigPhSite S).overMapPullbackExact f) ≅
      (smallPullbackExact f.left).comp (ExactFunctor.of (aInverseImage X)) :=
  (exactFunctor
      (Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u + 1})
      (Sheaf ((Scheme.bigPhSite S).over X) AddCommGrpCat.{u + 1})).isoMk
    (abelianSmallPhInverseImageSquare f)

/-- The bounded-below right-derived functor of topology-comparison direct image exists. -/
instance comparisonTopologyPushforwardAb_hasRightDerivedFunctor
    {S : Scheme.{u}} (X : Over S) :
    (comparisonTopologyPushforwardAb (etale_le_ph S) X).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf ((Scheme.bigPhSite S).over X) AddCommGrpCat.{u + 1})) := sorry

/-- The bounded-below right-derived functor of small étale direct image exists. -/
instance smallPushforwardAb_hasRightDerivedFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallPushforwardAb f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) := sorry

/-- The bounded-below right-derived functor of ph-slice direct image exists. -/
instance phPushforwardAb_hasRightDerivedFunctor
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    (phPushforwardAb f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf ((Scheme.bigPhSite S).over X) AddCommGrpCat.{u + 1})) := sorry

/-- Bounded-below derived inverse image `π_X⁻¹` on `D⁺`. -/
def plusPiInverseImage {S : Scheme.{u}} (X : Over S) :
    DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus
        (Sheaf ((S.overGrothendieckTopology @Etale).over X) AddCommGrpCat.{u + 1}) :=
  Plus.left (piExact X)

/-- Bounded-below derived inverse image `a_X⁻¹` on `D⁺`. -/
def plusAInverseImage {S : Scheme.{u}} (X : Over S) :
    DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus
        (Sheaf ((Scheme.bigPhSite S).over X) AddCommGrpCat.{u + 1}) :=
  Plus.left (ExactFunctor.of (aInverseImage X))

/-- Derived inverse image `a_X⁻¹` is the exact derived functor of abelian `a_X⁻¹`. -/
theorem plusAInverseImage_eq {S : Scheme.{u}} (X : Over S) :
    plusAInverseImage X = Plus.left (ExactFunctor.of (aInverseImage X)) := rfl

/-- Inverse-image square on `D⁺` induced by the abelian small/étale square. -/
def plusSmallEtaleInverseImageSquare {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    plusPiInverseImage Y ⋙
        Plus.left ((S.overGrothendieckTopology @Etale).overMapPullbackExact f) ≅
      Plus.left (smallPullbackExact f.left) ⋙ plusPiInverseImage X :=
  squareIso
    (piExact Y) ((S.overGrothendieckTopology @Etale).overMapPullbackExact f)
    (smallPullbackExact f.left) (piExact X)
    (abelianSmallEtaleExactSquare f)

/-- Inverse-image square `a_Y⁻¹ ⋙ f_big,ph⁻¹ ≅ f_small⁻¹ ⋙ a_X⁻¹` on `D⁺`. -/
def plusSmallPhInverseImageSquare {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    plusAInverseImage Y ⋙
        Plus.left ((Scheme.bigPhSite S).overMapPullbackExact f) ≅
      Plus.left (smallPullbackExact f.left) ⋙ plusAInverseImage X :=
  squareIso
    (ExactFunctor.of (aInverseImage Y))
    ((Scheme.bigPhSite S).overMapPullbackExact f)
    (smallPullbackExact f.left) (ExactFunctor.of (aInverseImage X))
    (abelianSmallPhExactSquare f)

/-- The morphism `f : X ⟶ Y` of schemes, viewed as an arrow in `Over Y`. -/
def overHomMk {X Y : Scheme.{u}} (f : X ⟶ Y) : Over.mk f ⟶ Over.mk (𝟙 Y) :=
  Over.homMk f

/-- A proper morphism of schemes, viewed in `Over Y`, lies in `properOver Y`. -/
theorem properOver_homMk {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    properOver Y (overHomMk f) := sorry

/-- Canonical `D⁺` mate `a_Y⁻¹ ∘ Rf_small,* ⟶ Rf_big,ph,* ∘ a_X⁻¹`. -/
def plusSmallPhPushforwardHom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Plus.right (smallPushforwardAb f) ⋙ plusAInverseImage (Over.mk (𝟙 Y)) ⟶
      plusAInverseImage (Over.mk f) ⋙ Plus.right (phPushforwardAb (overHomMk f)) :=
  DerivedBaseChange.map
    (Plus.adjunction (smallPullbackExact f) (smallPushforwardAb f)
      ((smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        Y.smallEtaleTopology X.smallEtaleTopology))
    (Plus.adjunction
      ((Scheme.bigPhSite Y).overMapPullbackExact (overHomMk f))
      (phPushforwardAb (overHomMk f))
      ((Scheme.bigPhSite Y).overMapCocontinuousAdjunction
        AddCommGrpCat.{u + 1} (overHomMk f)))
    (plusSmallPhInverseImageSquare (overHomMk f))

/-- `plusSmallPhPushforwardHom` is the right mate of the `D⁺` inverse-image square. -/
theorem plusSmallPhPushforwardHom_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    plusSmallPhPushforwardHom f =
      DerivedBaseChange.map
        (Plus.adjunction (smallPullbackExact f) (smallPushforwardAb f)
          ((smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
            Y.smallEtaleTopology X.smallEtaleTopology))
        (Plus.adjunction
          ((Scheme.bigPhSite Y).overMapPullbackExact (overHomMk f))
          (phPushforwardAb (overHomMk f))
          ((Scheme.bigPhSite Y).overMapCocontinuousAdjunction
            AddCommGrpCat.{u + 1} (overHomMk f)))
        (plusSmallPhInverseImageSquare (overHomMk f)) := rfl


/-- The bounded-below derived topology-comparison unit is an isomorphism on the inverse
image of a complex with locally torsion cohomology sheaves. -/
theorem plus_piInverseImage_unit_isIso {X : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (Sheaf.torsion X.smallEtaleTopology) K) :
    IsIso
      ((Derived.Plus.unit (etale_le_ph X) (Over.mk (𝟙 X))).app
        ((plusPiInverseImage (Over.mk (𝟙 X))).obj K)) := sorry

/-- The canonical bounded-below derived small-to-ph direct-image comparison is an
isomorphism for a proper morphism and a complex with locally torsion cohomology sheaves. -/
theorem proper_plusSmallPhPushforward_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (Sheaf.torsion X.smallEtaleTopology) K) :
    IsIso ((plusSmallPhPushforwardHom f).app K) := sorry


end AlgebraicGeometry.Scheme.PhComparison

end

end
