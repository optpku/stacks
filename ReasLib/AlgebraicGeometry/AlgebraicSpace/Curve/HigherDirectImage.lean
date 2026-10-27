/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.GeometricallyReducedConnected
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.H0Dim1
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Cohomology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.StructureSheaf

/-!
# Higher direct images of the structure sheaf on curves

The first higher direct image is degree-one cohomology of the unbounded derived
pushforward. For curve families with universally trivial structure-sheaf
pushforward and one-dimensional fibres, it is finite locally free and its
canonical comparison is invertible under arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The first higher direct image of the structure sheaf is the degree-one
cohomology sheaf of its unbounded derived pushforward. -/
abbrev higherDirectImageOne {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Y.Modules :=
  ModuleDerived.cohomologySheaf
    ((Modules.moduleDerivedPushforward f).obj (structureSheafDerived X)) 1

/-- The first higher direct image is computed by degree-one cohomology of the
derived pushforward of the structure sheaf in degree zero. -/
theorem higherDirectImageOne_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    higherDirectImageOne f =
      ModuleDerived.cohomologySheaf
        ((Modules.moduleDerivedPushforward f).obj (structureSheafDerived X)) 1 := sorry

/-- The canonical comparison from pullback of the first higher direct image of the
structure sheaf to the first higher direct image after arbitrary base change. -/
def higherDirectImageOneBaseChangeHom {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y' ⟶ Y) :
    (Modules.pullback g).obj (higherDirectImageOne f) ⟶
      higherDirectImageOne (pullback.snd f g) :=
  let OX := structureSheafDerived X
  let E := (Modules.moduleDerivedPushforward f).obj OX
  ModuleDerived.cohomologySheafPullbackComparison g E 1 ≫
    (DerivedCategory.homologyFunctor (Modules Y') 1).map
      ((DerivedBaseChange.map (derivedPullbackPushforwardAdjunction f)
          (derivedPullbackPushforwardAdjunction (pullback.snd f g))
          (DerivedQCoh.cohomologyBaseChangeCartesianIso
            (IsPullback.of_hasPullback f g))).app OX) ≫
    (DerivedCategory.homologyFunctor (Modules Y') 1).map
      ((Modules.moduleDerivedPushforward (pullback.snd f g)).map
        (ModuleDerived.structureSheafDerivedPullbackCounit (pullback.fst f g)))

/-- The first higher direct image base-change comparison is the cohomology-pullback
comparison followed by the derived base-change mate and the pushed-forward
structure-sheaf pullback counit on degree-one cohomology. -/
theorem higherDirectImageOneBaseChangeHom_eq {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    higherDirectImageOneBaseChangeHom f g =
      let OX := structureSheafDerived X
      let E := (Modules.moduleDerivedPushforward f).obj OX
      ModuleDerived.cohomologySheafPullbackComparison g E 1 ≫
        (DerivedCategory.homologyFunctor (Modules Y') 1).map
          ((DerivedBaseChange.map (derivedPullbackPushforwardAdjunction f)
              (derivedPullbackPushforwardAdjunction (pullback.snd f g))
              (DerivedQCoh.cohomologyBaseChangeCartesianIso
                (IsPullback.of_hasPullback f g))).app OX) ≫
        (DerivedCategory.homologyFunctor (Modules Y') 1).map
          ((Modules.moduleDerivedPushforward (pullback.snd f g)).map
            (ModuleDerived.structureSheafDerivedPullbackCounit (pullback.fst f g))) := sorry

/-- For a curve family with universally trivial structure-sheaf pushforward and
one-dimensional fibres, the structure-module pushforward unit is invertible
after every base change. -/
theorem unitToPushforward_isIso_universally {S : Scheme.{u}} (P : Obj S)
    (h : h0Dim1 S P) {Z : AlgebraicSpace S} (g : Z ⟶ ofOver (base P)) :
    IsIso (Modules.unitToPushforwardObjUnit (pullback.snd (hom P) g)) := sorry

/-- The first higher direct image of the structure sheaf of a curve family with
universally trivial structure-sheaf pushforward and one-dimensional fibres is
finite locally free. -/
theorem higherDirectImageOne_isFiniteLocallyFree {S : Scheme.{u}} (P : Obj S)
    (h : h0Dim1 S P) :
    SheafOfModules.IsFiniteLocallyFree (higherDirectImageOne (hom P)) := sorry

/-- For a curve family with universally trivial structure-sheaf pushforward and
one-dimensional fibres, the canonical first higher direct image comparison is
invertible under every base change. -/
theorem higherDirectImageOne_commutesWithBaseChange {S : Scheme.{u}} (P : Obj S)
    (h : h0Dim1 S P) {Z : AlgebraicSpace S} (g : Z ⟶ ofOver (base P)) :
    IsIso (higherDirectImageOneBaseChangeHom (hom P) g) := sorry

/-- Curve families with reduced, connected geometric fibres of dimension one
have universally trivial structure-sheaf pushforward and fibres of dimension one. -/
theorem geometricallyReducedConnectedDim1_le_h0Dim1 (S : Scheme.{u}) :
    geometricallyReducedConnectedDim1 S ≤ h0Dim1 S := sorry

namespace HigherDirectImageOne

/-- The first higher direct image of the structure sheaf of a curve family with
reduced, connected geometric fibres of dimension one is finite locally free. -/
theorem isFiniteLocallyFree_of_reducedConnected
    {S : Scheme.{u}} (P : Obj S) (h : geometricallyReducedConnectedDim1 S P) :
    SheafOfModules.IsFiniteLocallyFree (higherDirectImageOne (hom P)) := sorry

/-- For a curve family with reduced, connected geometric fibres of dimension one,
the canonical first higher direct image comparison is invertible under arbitrary
base change. -/
theorem isIso_baseChange_of_reducedConnected
    {S : Scheme.{u}} (P : Obj S) (h : geometricallyReducedConnectedDim1 S P)
    {Z : AlgebraicSpace S} (g : Z ⟶ ofOver (base P)) :
    IsIso (higherDirectImageOneBaseChangeHom (hom P) g) := sorry

end HigherDirectImageOne

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
