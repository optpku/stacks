module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.AbelianComparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.DerivedComparison

/-!
# Bounded-below derived small-étale to h comparison

Exact inverse-image squares induce bounded-below derived inverse images and their canonical
direct-image mate. The comparison unit and proper direct-image mate are isomorphisms for
complexes with locally torsion cohomology sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale.SmallToBig

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.HComparison

variable {X Y : Scheme.{u}}

/-- Exact inverse image `π_X⁻¹` on abelian small-étale sheaves. -/
abbrev piExact (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ₑ
      Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1} :=
  ExactFunctor.of (AlgebraicGeometry.Scheme.FppfEtale.piInverseImage X)

/-- Bundled exact-functor form of the abelian small-étale inverse-image square. -/
def abelianSmallEtaleExactSquare (f : X ⟶ Y) :
    (piExact Y).comp (etaleTopology.overMapPullbackExact f) ≅
      (AlgebraicGeometry.Scheme.PhComparison.smallPullbackExact f).comp (piExact X) :=
  (exactFunctor
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
      (Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1})).isoMk
    (abelianSmallEtaleInverseImageSquare f)

/-- Bundled exact-functor form of the abelian small-to-h inverse-image square. -/
def abelianSmallHExactSquare (f : X ⟶ Y) :
    (ExactFunctor.of (aInverseImage Y)).comp
        (hPrecoverage.toGrothendieck.overMapPullbackExact f) ≅
      (AlgebraicGeometry.Scheme.PhComparison.smallPullbackExact f).comp (ExactFunctor.of (aInverseImage X)) :=
  (exactFunctor
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
      (Sheaf (hPrecoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1})).isoMk
    (abelianSmallHInverseImageSquare f)

/-- The bounded-below right-derived functor of topology-comparison direct image exists. -/
instance comparisonTopologyPushforwardAb_hasRightDerivedFunctor (X : Scheme.{u}) :
    (comparisonTopologyPushforwardAb etale_le_h X).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (hPrecoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1})) := sorry

/-- Cocontinuous direct image of abelian sheaves on big h slices. -/
abbrev hPushforwardAb (f : X ⟶ Y) :
    Sheaf (hPrecoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (hPrecoverage.toGrothendieck.over Y) AddCommGrpCat.{u + 1} :=
  (Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
    (hPrecoverage.toGrothendieck.over X) (hPrecoverage.toGrothendieck.over Y)

/-- `hPushforwardAb` is the cocontinuous sheaf pushforward along `Over.map`. -/
theorem hPushforwardAb_eq (f : X ⟶ Y) :
    hPushforwardAb f =
      (Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (hPrecoverage.toGrothendieck.over X)
        (hPrecoverage.toGrothendieck.over Y) := rfl

/-- The bounded-below right-derived functor of big h direct image exists. -/
instance hPushforwardAb_hasRightDerivedFunctor (f : X ⟶ Y) :
    (hPushforwardAb f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (hPrecoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1})) := sorry

/-- Bounded-below derived inverse image `π_X⁻¹` on `D⁺`. -/
def plusPiInverseImage (X : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1}) :=
  ExactFunctor.Derived.Plus.functor (piExact X)

/-- Bounded-below derived inverse image `a_X⁻¹` on `D⁺`. -/
def plusAInverseImage (X : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus
        (Sheaf (hPrecoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1}) :=
  ExactFunctor.Derived.Plus.functor (ExactFunctor.of (aInverseImage X))

/-- Derived inverse image `a_X⁻¹` is the exact derived functor of abelian `a_X⁻¹`. -/
theorem plusAInverseImage_eq (X : Scheme.{u}) :
    plusAInverseImage X =
      ExactFunctor.Derived.Plus.functor (ExactFunctor.of (aInverseImage X)) := rfl

/-- Inverse-image square on `D⁺` induced by the abelian small/étale square. -/
def plusSmallEtaleInverseImageSquare (f : X ⟶ Y) :
    plusPiInverseImage Y ⋙
        ExactFunctor.Derived.Plus.functor (etaleTopology.overMapPullbackExact f) ≅
      ExactFunctor.Derived.Plus.functor (AlgebraicGeometry.Scheme.PhComparison.smallPullbackExact f) ⋙
        plusPiInverseImage X :=
  ExactFunctor.Derived.Plus.squareIso
    (piExact Y) (etaleTopology.overMapPullbackExact f)
    (AlgebraicGeometry.Scheme.PhComparison.smallPullbackExact f) (piExact X)
    (abelianSmallEtaleExactSquare f)

/-- Inverse-image square `a_Y⁻¹ ⋙ f_big,h⁻¹ ≅ f_small⁻¹ ⋙ a_X⁻¹` on `D⁺`. -/
def plusSmallHInverseImageSquare (f : X ⟶ Y) :
    plusAInverseImage Y ⋙
        ExactFunctor.Derived.Plus.functor
          (hPrecoverage.toGrothendieck.overMapPullbackExact f) ≅
      ExactFunctor.Derived.Plus.functor (AlgebraicGeometry.Scheme.PhComparison.smallPullbackExact f) ⋙
        plusAInverseImage X :=
  ExactFunctor.Derived.Plus.squareIso
    (ExactFunctor.of (aInverseImage Y))
    (hPrecoverage.toGrothendieck.overMapPullbackExact f)
    (AlgebraicGeometry.Scheme.PhComparison.smallPullbackExact f) (ExactFunctor.of (aInverseImage X))
    (abelianSmallHExactSquare f)

/-- Canonical `D⁺` mate `a_Y⁻¹ ∘ Rf_small,* ⟶ Rf_big,h,* ∘ a_X⁻¹`. -/
def plusSmallHPushforwardHom (f : X ⟶ Y) :
    Adjunction.Derived.Plus.right (AlgebraicGeometry.Scheme.PhComparison.smallPushforwardAb f) ⋙ plusAInverseImage Y ⟶
      plusAInverseImage X ⋙ Adjunction.Derived.Plus.right (hPushforwardAb f) :=
  DerivedBaseChange.map
    (Adjunction.Derived.Plus.adjunction (AlgebraicGeometry.Scheme.PhComparison.smallPullbackExact f)
      (AlgebraicGeometry.Scheme.PhComparison.smallPushforwardAb f)
      ((smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        Y.smallEtaleTopology X.smallEtaleTopology))
    (Adjunction.Derived.Plus.adjunction
      (hPrecoverage.toGrothendieck.overMapPullbackExact f)
      (hPushforwardAb f)
      (hPrecoverage.toGrothendieck.overMapCocontinuousAdjunction
        AddCommGrpCat.{u + 1} f))
    (plusSmallHInverseImageSquare f)

/-- `plusSmallHPushforwardHom` is the right mate of the `D⁺` inverse-image square. -/
theorem plusSmallHPushforwardHom_eq (f : X ⟶ Y) :
    plusSmallHPushforwardHom f =
      DerivedBaseChange.map
        (Adjunction.Derived.Plus.adjunction (AlgebraicGeometry.Scheme.PhComparison.smallPullbackExact f)
          (AlgebraicGeometry.Scheme.PhComparison.smallPushforwardAb f)
          ((smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
            Y.smallEtaleTopology X.smallEtaleTopology))
        (Adjunction.Derived.Plus.adjunction
          (hPrecoverage.toGrothendieck.overMapPullbackExact f)
          (hPushforwardAb f)
          (hPrecoverage.toGrothendieck.overMapCocontinuousAdjunction
            AddCommGrpCat.{u + 1} f))
        (plusSmallHInverseImageSquare f) := rfl

/-- The derived h-to-étale comparison unit is an isomorphism on the small-to-big
inverse image of a bounded-below complex with locally torsion cohomology sheaves. -/
theorem plus_piInverseImage_unit_isIso {X : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (Sheaf.torsion X.smallEtaleTopology) K) :
    IsIso
      ((Derived.Plus.unit etale_le_h X).app ((plusPiInverseImage X).obj K)) :=
  sorry

/-- The canonical derived direct-image mate for small-to-h inverse image is an
isomorphism along a proper morphism on bounded-below complexes with locally torsion cohomology. -/
theorem proper_plusSmallHPushforward_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (Sheaf.torsion X.smallEtaleTopology) K) :
    IsIso ((plusSmallHPushforwardHom f).app K) := sorry

end AlgebraicGeometry.Scheme.HComparison

end

end
