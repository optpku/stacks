/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Sheafification
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Composition

@[expose] public section

/-!
# Derived base change for inverse-image closed subsets

This module constructs derived pullback between closed-subset module categories and the canonical
base-change mate for the cartesian square formed by a closed-subspace inclusion and its inverse
image.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ClosedSubset.InverseImage

variable {X Y : RingedSpace.{u}}

/-- Derived pullback between closed-subset module categories along the morphism induced on an
inverse-image closed subset. -/
noncomputable def derivedPullback (f : X ⟶ Y) (Z : Closeds Y) :
    ClosedSubset.ModuleDerived Y Z ⥤
      ClosedSubset.ModuleDerived X (ClosedSubset.preimage f Z) :=
  (ClosedSubset.moduleEquivalence Y Z).mapDerivedCategory.inverse ⋙
    RingedSpace.modulePullbackDerived (ClosedSubset.restrictedHom f Z) ⋙
    (ClosedSubset.moduleEquivalence X
      (ClosedSubset.preimage f Z)).mapDerivedCategory.functor

/-- The inverse-image closed-subset derived pullback is the intrinsic derived pullback transported
through the canonical module-presentation equivalences. -/
theorem derivedPullback_def (f : X ⟶ Y) (Z : Closeds Y) :
    derivedPullback f Z =
      (ClosedSubset.moduleEquivalence Y Z).mapDerivedCategory.inverse ⋙
        RingedSpace.modulePullbackDerived (ClosedSubset.restrictedHom f Z) ⋙
        (ClosedSubset.moduleEquivalence X
          (ClosedSubset.preimage f Z)).mapDerivedCategory.functor := sorry

/-- The canonical derived-pullback square for a closed-subspace inclusion and its inverse image. -/
noncomputable def pullbackSquareIso (f : X ⟶ Y) (Z : Closeds Y) :
    RingedSpace.modulePullbackDerived f ⋙
        RingedSpace.modulePullbackDerived
          (ClosedSubset.inclusionHom X (ClosedSubset.preimage f Z)) ≅
      RingedSpace.modulePullbackDerived (ClosedSubset.inclusionHom Y Z) ⋙
        RingedSpace.modulePullbackDerived (ClosedSubset.restrictedHom f Z) :=
  RingedSpace.Hom.DerivedBaseChange.pullbackIsoOfCompIso
    (CommSq.mk (ClosedSubset.restrictedHom_fac f Z))
    (RingedSpace.modulePullbackDerived.compIso
      (ClosedSubset.inclusionHom X (ClosedSubset.preimage f Z)) f
      (RingedSpace.modulePullbackDerived.compComparison_isIso _ _))
    (RingedSpace.modulePullbackDerived.compIso
      (ClosedSubset.restrictedHom f Z) (ClosedSubset.inclusionHom Y Z)
      (RingedSpace.modulePullbackDerived.compComparison_isIso _ _))

/-- The canonical derived base-change mate for an inverse-image closed subset. -/
noncomputable def intrinsicBaseChangeMap (f : X ⟶ Y) (Z : Closeds Y) :
    RingedSpace.moduleDerivedPushforward (ClosedSubset.inclusionHom Y Z) ⋙
        RingedSpace.modulePullbackDerived f ⟶
      RingedSpace.modulePullbackDerived (ClosedSubset.restrictedHom f Z) ⋙
        RingedSpace.moduleDerivedPushforward
          (ClosedSubset.inclusionHom X (ClosedSubset.preimage f Z)) :=
  RingedSpace.Hom.DerivedBaseChange.map
    (ClosedSubset.Inclusion.derivedAdjunction Y Z)
    (ClosedSubset.Inclusion.derivedAdjunction X (ClosedSubset.preimage f Z))
    (pullbackSquareIso f Z)

/-- The canonical inverse-image closed-subset derived base-change mate is invertible. -/
noncomputable instance intrinsicBaseChangeMap_isIso (f : X ⟶ Y) (Z : Closeds Y) :
    IsIso (intrinsicBaseChangeMap f Z) := sorry

/-- The canonical inverse-image closed-subset derived base-change isomorphism. -/
noncomputable def intrinsicBaseChangeIso (f : X ⟶ Y) (Z : Closeds Y) :
    RingedSpace.moduleDerivedPushforward (ClosedSubset.inclusionHom Y Z) ⋙
        RingedSpace.modulePullbackDerived f ≅
      RingedSpace.modulePullbackDerived (ClosedSubset.restrictedHom f Z) ⋙
        RingedSpace.moduleDerivedPushforward
          (ClosedSubset.inclusionHom X (ClosedSubset.preimage f Z)) :=
  asIso (intrinsicBaseChangeMap f Z)

/-- The inverse-image closed-subset derived pullback followed by closed-subset direct image is
canonically isomorphic to ambient derived pullback after closed-subset direct image. -/
noncomputable def derivedPushforwardIso (f : X ⟶ Y) (Z : Closeds Y) :
    derivedPullback f Z ⋙
        ClosedSubset.Pushforward.derived X (ClosedSubset.preimage f Z) ≅
      ClosedSubset.Pushforward.derived Y Z ⋙
        RingedSpace.modulePullbackDerived f :=
  let eY := ClosedSubset.moduleDerivedEquivalence Y Z
  let eX := ClosedSubset.moduleDerivedEquivalence X (ClosedSubset.preimage f Z)
  let pull := RingedSpace.modulePullbackDerived (ClosedSubset.restrictedHom f Z)
  let pushY := ClosedSubset.Pushforward.derived Y Z
  let pushX := ClosedSubset.Pushforward.derived X (ClosedSubset.preimage f Z)
  let derivedPushY := RingedSpace.moduleDerivedPushforward (ClosedSubset.inclusionHom Y Z)
  let derivedPushX := RingedSpace.moduleDerivedPushforward
    (ClosedSubset.inclusionHom X (ClosedSubset.preimage f Z))
  (Functor.associator (eY.inverse ⋙ pull) eX.functor pushX) ≪≫
    Functor.isoWhiskerLeft (eY.inverse ⋙ pull)
      (ClosedSubset.Intrinsic.Pushforward.comparison X (ClosedSubset.preimage f Z)) ≪≫
    Functor.associator eY.inverse pull derivedPushX ≪≫
    Functor.isoWhiskerLeft eY.inverse (intrinsicBaseChangeIso f Z).symm ≪≫
    (Functor.associator eY.inverse derivedPushY
      (RingedSpace.modulePullbackDerived f)).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.isoWhiskerLeft eY.inverse
          (ClosedSubset.Intrinsic.Pushforward.comparison Y Z)).symm ≪≫
        (Functor.associator eY.inverse eY.functor pushY).symm ≪≫
        Functor.isoWhiskerRight eY.counitIso pushY ≪≫
        Functor.leftUnitor pushY)
      (RingedSpace.modulePullbackDerived f)

end AlgebraicGeometry.RingedSpace.ClosedSubset.InverseImage
