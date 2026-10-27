/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Composition.Canonical
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Monoidal

@[expose] public section

/-!
# Monoidal compatibility of derived-pushforward composition

The canonical comparison from the derived pushforward of a composite to iterated derived
pushforward intertwines relative cup products as soon as that comparison has been identified as
a monoidal natural transformation. Keeping this coherence premise visible avoids inferring it
from unrelated objectwise tensor isomorphisms.
-/

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe z uX vX uY vY uZ vZ w

namespace RingedSite.Hom.modulePushforwardDerived

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  {Z : RingedSite.{uZ, vZ, w}}
variable (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y Z)
variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
  [UnivLE.{max uZ vZ, z}]
variable [(f.modulePushforward.{z}).IsRightAdjoint]
variable [(g.modulePushforward.{z}).IsRightAdjoint]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} g) (ModuleQis.{z} Y)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} (f.comp g)) (ModuleQis.{z} X)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} f) (ModuleQis.{z} Y)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} g) (ModuleQis.{z} Z)]
variable [Functor.HasLeftDerivedFunctor
  (compositePullbackToDerived.{z} f g) (ModuleQis.{z} Z)]
variable [DerivedAdjunction.HasPair.{z} f]
variable [DerivedAdjunction.HasPair.{z} g]
variable [compositeDerivedPair.{z} f g]
variable [MonoidalCategory (ModuleDerived.{z} X)]
variable [MonoidalCategory (ModuleDerived.{z} Y)]
variable [MonoidalCategory (ModuleDerived.{z} Z)]
variable [(modulePullbackDerived.{z} f).OplaxMonoidal]
variable [(modulePullbackDerived.{z} g).OplaxMonoidal]
variable [(compositePullbackDerived.{z} f g).OplaxMonoidal]

/-- The canonical lax monoidal structure on derived pushforward along a composite. -/
@[implicit_reducible]
def compositeLaxMonoidal : (modulePushforwardDerived.{z} (f.comp g)).LaxMonoidal :=
  @laxMonoidal.{z} _ _ (f.comp g) inferInstance inferInstance
    (modulePushforwardComp_isRightAdjoint f g) inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance

/-- The canonical derived-pushforward composition comparison is monoidal relative to the
adjunction-induced lax structures and their composite. -/
def compComparisonIsMonoidal
    (h_comparison : IsIso (modulePullbackDerived.compComparison f g)) : Prop :=
  @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ (compComparison f g h_comparison)
    (compositeLaxMonoidal f g)
    (@Functor.LaxMonoidal.comp _ _ _ _ _ _ _ _ _
      (modulePushforwardDerived.{z} f) (modulePushforwardDerived.{z} g)
      (laxMonoidal f) (laxMonoidal g))

/-- A monoidal derived-pushforward composition comparison intertwines the relative cup product
for the composite with the iterated relative cup product. -/
@[stacks 0FPN]
theorem cupProduct_compComparison
    (h_comparison : IsIso (modulePullbackDerived.compComparison f g))
    (h_monoidal : compComparisonIsMonoidal f g h_comparison)
    (K L : ModuleDerived.{z} X) :
    (@cupProduct.{z} _ _ (f.comp g) inferInstance inferInstance
      (modulePushforwardComp_isRightAdjoint f g) inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance K L) ≫
        (compComparison f g h_comparison).app (K ⊗ L) =
      ((compComparison f g h_comparison).app K ⊗ₘ
          (compComparison f g h_comparison).app L) ≫
        cupProduct g
          ((modulePushforwardDerived.{z} f).obj K)
          ((modulePushforwardDerived.{z} f).obj L) ≫
        (modulePushforwardDerived.{z} g).map (cupProduct f K L) := sorry

end RingedSite.Hom.modulePushforwardDerived
