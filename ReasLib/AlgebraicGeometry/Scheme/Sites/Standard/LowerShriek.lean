module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf
public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
public import Mathlib.CategoryTheory.Limits.ExactFunctor

/-!
# Lower shriek on standard big sites

This module provides the additive and module lower-shriek constructions associated to a morphism
of schemes and a standard big-site topology.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.StandardTopology.Big

/-- Postcomposition along a scheme morphism is continuous for every standard big topology. -/
instance map_isContinuous (τ : StandardTopology) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Over.map f).IsContinuous (τ.overTopology X) (τ.overTopology Y) := sorry

/-- Postcomposition along a scheme morphism is cocontinuous for every standard big topology. -/
instance map_isCocontinuous (τ : StandardTopology) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Over.map f).IsCocontinuous (τ.overTopology X) (τ.overTopology Y) := sorry

/-- The inverse-image functor on additive sheaves induced by postcomposition. -/
abbrev additiveInverseImage (τ : StandardTopology) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf (τ.overTopology Y) AddCommGrpCat.{u + 1} ⥤
      Sheaf (τ.overTopology X) AddCommGrpCat.{u + 1} :=
  (Over.map f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (τ.overTopology X) (τ.overTopology Y)

/-- The additive lower-shriek functor induced by postcomposition. -/
abbrev additiveLowerShriek (τ : StandardTopology) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf (τ.overTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (τ.overTopology Y) AddCommGrpCat.{u + 1} :=
  (Over.map f).sheafPullback AddCommGrpCat.{u + 1}
    (τ.overTopology X) (τ.overTopology Y)

/-- The module inverse-image functor over the structure sheaf on the target site. -/
abbrev modulePullback (τ : StandardTopology) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SheafOfModules.{u + 1} (structureSheaf τ Y) ⥤
      SheafOfModules.{u + 1} (structureSheaf τ X) :=
  RingedSite.Cocontinuous.moduleInverseImage
    (J := τ.overTopology X) (K := τ.overTopology Y)
    (Over.map f) (structureSheaf τ Y)

/-- The module lower-shriek functor induced by postcomposition. -/
abbrev moduleLowerShriek (τ : StandardTopology) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SheafOfModules.{u + 1} (structureSheaf τ X) ⥤
      SheafOfModules.{u + 1} (structureSheaf τ Y) :=
  RingedSite.Cocontinuous.moduleLowerShriek
    (J := τ.overTopology X) (K := τ.overTopology Y)
    (Over.map f) (structureSheaf τ Y)

/-- The canonical comparison from additive lower shriek to the underlying module lower shriek. -/
def underlyingComparison (τ : StandardTopology) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SheafOfModules.toSheaf.{u + 1} (structureSheaf τ X) ⋙
        additiveLowerShriek τ f ⟶
      moduleLowerShriek τ f ⋙ SheafOfModules.toSheaf.{u + 1} (structureSheaf τ Y) :=
  RingedSite.Cocontinuous.moduleLowerShriek.underlyingComparison.{u, u + 1,
      u + 1, u + 1, u, u}
    (J := τ.overTopology X) (K := τ.overTopology Y)
    (Over.map f) (structureSheaf τ Y)

/-- The adjunction between additive lower shriek and additive inverse image. -/
noncomputable def additiveLowerShriekAdjunction (τ : StandardTopology)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    additiveLowerShriek τ f ⊣ additiveInverseImage τ f :=
  (Over.map f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (τ.overTopology X) (τ.overTopology Y)

/-- Additive lower shriek on a standard big site preserves finite limits and finite colimits. -/
theorem additiveLowerShriek_exact (τ : StandardTopology)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    exactFunctor
      (Sheaf (τ.overTopology X) AddCommGrpCat.{u + 1})
      (Sheaf (τ.overTopology Y) AddCommGrpCat.{u + 1})
      (additiveLowerShriek τ f) := sorry

/-- The adjunction between module lower shriek and module inverse image. -/
noncomputable def moduleLowerShriekAdjunction (τ : StandardTopology)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    moduleLowerShriek τ f ⊣ modulePullback τ f :=
  RingedSite.Cocontinuous.moduleLowerShriek.adjunction
    (J := τ.overTopology X) (K := τ.overTopology Y)
    (Over.map f) (structureSheaf τ Y)

/-- Module lower shriek on a standard big ringed site preserves finite limits and finite colimits. -/
theorem moduleLowerShriek_exact (τ : StandardTopology)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    exactFunctor
      (SheafOfModules.{u + 1} (structureSheaf τ X))
      (SheafOfModules.{u + 1} (structureSheaf τ Y))
      (moduleLowerShriek τ f) := sorry

/-- The canonical underlying comparison is an isomorphism on standard big sites. -/
instance underlyingComparison_isIso (τ : StandardTopology)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (underlyingComparison τ f) := sorry

end AlgebraicGeometry.StandardTopology.Big
