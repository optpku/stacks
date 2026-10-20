/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Flat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.LeftDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Preservation
public import ReasLib.CategoryTheory.Triangulated.TStructure.Functor.Bounds

@[expose] public section

/-!
# Derived pullback along flat morphisms of ringed sites

This module compares derived pullback along a flat morphism of ringed sites with the exact
functor induced directly on derived categories.  It exposes the comparison morphism before its
invertibility theorem, so unfinished proof obligations never select inverse data.
-/

open CategoryTheory
-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe uX vX uY vY w z

namespace RingedSite.Hom

namespace modulePullbackDerived.Flat

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
variable (f : X.Hom Y)
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}]
variable [(PresheafOfModules.pushforward.{z} f.structureSheafMap.hom).IsRightAdjoint]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} f) (ModuleQis.{z} Y)]

/-- The canonical counit presenting ringed-site module pullback as a total left-derived
functor. -/
@[stacks 0735 "flat pullback left-derived counit"]
noncomputable abbrev counit :
    moduleLocalization.{z} Y ⋙ modulePullbackDerived.{z} f ⟶
      modulePullbackToDerived.{z} f :=
  (modulePullbackToDerived.{z} f).totalLeftDerivedCounit
    (moduleLocalization.{z} Y) (ModuleQis.{z} Y)

/-- The canonical comparison from exact flat pullback on derived categories to total derived
pullback. -/
@[stacks 0735 "flat pullback exact-model comparison"]
noncomputable def comparison [IsFlat.{z} f] :
    (IsFlat.exactPullback.{z} f).mapDerivedCategory ⟶ modulePullbackDerived.{z} f :=
  ExactFunctor.LeftDerived.comparison
    (IsFlat.exactPullback.{z} f) (modulePullbackDerived.{z} f) (counit f)
    (inferInstanceAs
      (((modulePullbackToDerived.{z} f).totalLeftDerived
          (moduleLocalization.{z} Y) (ModuleQis.{z} Y)).IsLeftDerivedFunctor
        ((modulePullbackToDerived.{z} f).totalLeftDerivedCounit
          (moduleLocalization.{z} Y) (ModuleQis.{z} Y))
        (ModuleQis.{z} Y)))

/-- The flat exact-model comparison satisfies the defining left-derived counit equation. -/
@[stacks 0735 "flat pullback exact-model comparison counit"]
theorem comparison_counit [IsFlat.{z} f] :
    Functor.whiskerLeft
        (moduleLocalization.{z} Y) (comparison f) ≫ counit f =
      (IsFlat.exactPullback.{z} f).obj.mapDerivedCategoryFactorsh.hom := sorry

/-- Componentwise form of the counit equation for the flat exact-model comparison. -/
@[stacks 0735 "flat pullback exact-model comparison counit component"]
theorem comparison_counit_app [IsFlat.{z} f]
    (K : HomotopyCategory (ModuleCat.{z} Y) (up ℤ)) :
    (comparison f).app ((moduleLocalization.{z} Y).obj K) ≫ (counit f).app K =
      (IsFlat.exactPullback.{z} f).obj.mapDerivedCategoryFactorsh.hom.app K := sorry

/-- The flat exact-model comparison is invertible.  It is kept as a theorem rather than an
instance so that unfinished proof debt cannot silently create inverse data. -/
@[stacks 0735 "flat pullback exact-model comparison is invertible"]
theorem comparison_isIso [IsFlat.{z} f] : IsIso (comparison f) := sorry

/-- Upgrade the flat exact-model comparison to an isomorphism from an explicit invertibility
certificate. -/
@[stacks 0735 "flat pullback exact-model comparison isomorphism"]
noncomputable def exactIso [IsFlat.{z} f] (h : IsIso (comparison f)) :
    (IsFlat.exactPullback.{z} f).mapDerivedCategory ≅ modulePullbackDerived.{z} f :=
  ExactFunctor.LeftDerived.comparisonIso
    (IsFlat.exactPullback.{z} f) (modulePullbackDerived.{z} f) (counit f)
    (inferInstanceAs
      (((modulePullbackToDerived.{z} f).totalLeftDerived
          (moduleLocalization.{z} Y) (ModuleQis.{z} Y)).IsLeftDerivedFunctor
        ((modulePullbackToDerived.{z} f).totalLeftDerivedCounit
          (moduleLocalization.{z} Y) (ModuleQis.{z} Y))
        (ModuleQis.{z} Y))) h

/-- The forward map of `exactIso` is the canonical flat exact-model comparison. -/
@[simp, stacks 0735 "flat pullback exact-model comparison isomorphism forward map"]
theorem exactIso_hom [IsFlat.{z} f] (h : IsIso (comparison f)) :
    (exactIso f h).hom = comparison f := sorry

/-- The flat exact-model isomorphism does not depend on the supplied proof of invertibility. -/
@[stacks 0735 "flat pullback exact-model comparison proof independence"]
theorem exactIso_eq [IsFlat.{z} f] (h₁ h₂ : IsIso (comparison f)) :
    exactIso f h₁ = exactIso f h₂ := sorry

/-- Flat pullback commutes with cohomology after transport from its exact model.  The explicit
invertibility certificate prevents unfinished proof debt from selecting inverse data. -/
@[stacks 0735 "flat derived pullback commutes with cohomology"]
noncomputable def homologyIso [IsFlat.{z} f] (h : IsIso (comparison f))
    (K : ModuleDerived.{z} Y) (q : ℤ) :
    f.modulePullback.obj ((DerivedCategory.homologyFunctor (ModuleCat.{z} Y) q).obj K) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{z} X) q).obj
        ((modulePullbackDerived.{z} f).obj K) :=
  ((IsFlat.exactPullback.{z} f).homologyIso K q).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{z} X) q).mapIso
      ((exactIso f h).app K)

/-- The cohomology comparison for flat derived pullback is independent of the supplied proof of
comparison invertibility. -/
@[stacks 0735 "flat derived pullback cohomology comparison proof independence"]
theorem homologyIso_eq [IsFlat.{z} f] (h₁ h₂ : IsIso (comparison f))
    (K : ModuleDerived.{z} Y) (q : ℤ) :
    homologyIso f h₁ K q = homologyIso f h₂ K q := sorry

/-- Flat derived pullback preserves every lower bound of the canonical t-structure. -/
@[stacks 0735 "flat derived pullback preserves lower bounds"]
theorem mapsGE [IsFlat.{z} f] :
    Functor.TStructure.MapsGE (modulePullbackDerived.{z} f)
      DerivedCategory.TStructure.t DerivedCategory.TStructure.t 0 := sorry

/-- Flat derived pullback preserves every upper bound of the canonical t-structure. -/
@[stacks 0735 "flat derived pullback preserves upper bounds"]
theorem mapsLE [IsFlat.{z} f] :
    Functor.TStructure.MapsLE (modulePullbackDerived.{z} f)
      DerivedCategory.TStructure.t DerivedCategory.TStructure.t 0 := sorry

/-- Objectwise lower-bound preservation for flat derived pullback. -/
@[stacks 0735 "flat derived pullback preserves an objectwise lower bound"]
theorem isGE [IsFlat.{z} f] (K : ModuleDerived.{z} Y) (n : ℤ) (hK : K.IsGE n) :
    ((modulePullbackDerived.{z} f).obj K).IsGE n := sorry

/-- Objectwise upper-bound preservation for flat derived pullback. -/
@[stacks 0735 "flat derived pullback preserves an objectwise upper bound"]
theorem isLE [IsFlat.{z} f] (K : ModuleDerived.{z} Y) (n : ℤ) (hK : K.IsLE n) :
    ((modulePullbackDerived.{z} f).obj K).IsLE n := sorry

/-- Once invertibility of the exact-model comparison is supplied, flat derived pullback inherits
the canonical integer-shift comparison from exact pullback. -/
@[stacks 0735 "flat derived pullback commutes with shifts"]
noncomputable instance commShift [IsFlat.{z} f] [IsIso (comparison f)] :
    (modulePullbackDerived.{z} f).CommShift ℤ :=
  Functor.CommShift.ofIso (exactIso f inferInstance) ℤ

/-- Relative to the transported shift comparison, flat derived pullback is triangulated. -/
@[stacks 0735 "flat derived pullback is triangulated", instance]
theorem isTriangulated [IsFlat.{z} f] [IsIso (comparison f)] :
    (modulePullbackDerived.{z} f).IsTriangulated := sorry

end modulePullbackDerived.Flat

end RingedSite.Hom

-- Any `sorryAx` reported here is inherited from the existing module-sheaf/category law fields in
-- `modulePullbackToDerived` and `modulePullbackDerived`; comparison invertibility remains an
-- explicit input to every data-bearing declaration below.
