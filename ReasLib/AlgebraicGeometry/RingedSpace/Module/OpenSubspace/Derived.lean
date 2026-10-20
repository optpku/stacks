/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Restriction
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.LeftDerived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Restriction
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived restriction to open subspaces

This file owns derived categories of modules on open subspaces and the functors induced by
restriction.  The comparison isomorphisms are stated at the `mapDerivedCategory` level so that
downstream arguments can work directly with complexes and with arbitrary derived objects.
-/

open AlgebraicGeometry
open CategoryTheory
open ComplexShape
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The derived category `D(𝒪_U)` of modules on the open subspace `U` of `X`. -/
@[stacks 08DP "derived category on an open subspace"]
abbrev moduleDerivedOnOpen (X : RingedSpace.{u}) (U : Opens X.carrier) :=
  DerivedCategory (openSubspaceModuleCategory X U)

/-- Restriction of a derived `𝒪_X`-module to the open subspace `U`. -/
@[stacks 08DP "derived restriction to an open subspace"]
abbrev moduleRestrictionToOpenDerived
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    DerivedCategory (RingedSpace.Modules X) ⥤ moduleDerivedOnOpen X U :=
  (OpenSubspace.Restriction.exact X U).mapDerivedCategory

/-- Restriction of bounded-below derived `𝒪_X`-modules to the open subspace `U`. -/
@[stacks 01E5 "bounded-below derived restriction to an open subspace"]
noncomputable abbrev moduleRestrictionToOpenDerivedPlus
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    DerivedCategory.Plus (RingedSpace.Modules X) ⥤
      DerivedCategory.Plus (openSubspaceModuleCategory X U) :=
  ExactFunctor.Derived.Plus.functor (OpenSubspace.Restriction.exact X U)

/-- Forgetting the bounded-below restriction recovers derived restriction on the ambient
derived categories. -/
@[stacks 01E5 "bounded-below restriction and ambient derived restriction"]
noncomputable abbrev moduleRestrictionToOpenDerivedPlusCompιIso
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    moduleRestrictionToOpenDerivedPlus X U ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ moduleRestrictionToOpenDerived X U :=
  ExactFunctor.Derived.Plus.compιIso (OpenSubspace.Restriction.exact X U)

/-- Derived restriction to an open subspace is additive. -/
theorem moduleRestrictionToOpenDerived_additive
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleRestrictionToOpenDerived X U).Additive := sorry

/-- The canonical comparison between derived restriction of `K` and the derived object of its
restricted cochain complex. -/
abbrev moduleRestrictionToOpenDerivedFactors
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    (K : CochainComplex (RingedSpace.Modules X) ℤ) :
    (moduleRestrictionToOpenDerived X U).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((moduleRestrictionComplexToOpen X U).obj K) :=
  (OpenSubspace.Restriction.exact X U).obj.mapDerivedCategoryFactors.app K

/-- The comparison for derived restriction is natural in a morphism of cochain complexes. -/
theorem OpenSubspace.Restriction.derivedFactors_naturality
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    {K L : CochainComplex (RingedSpace.Modules X) ℤ} (f : K ⟶ L) :
    (moduleRestrictionToOpenDerived X U).map (DerivedCategory.Q.map f) ≫
        (moduleRestrictionToOpenDerivedFactors X U L).hom =
      (moduleRestrictionToOpenDerivedFactors X U K).hom ≫
        DerivedCategory.Q.map ((moduleRestrictionComplexToOpen X U).map f) := sorry

namespace OpenSubspace.Restriction

/-- Restriction between nested open subspaces is additive. -/
theorem betweenAdditive (X : RingedSpace.{u})
    {W U : Opens X.carrier} (h : W ≤ U) :
    (moduleRestrictionBetweenOpens X h).Additive := sorry

/-- Restriction between nested open subspaces preserves finite limits. -/
theorem betweenPreservesFiniteLimits (X : RingedSpace.{u})
    {W U : Opens X.carrier} (h : W ≤ U) :
    Limits.PreservesFiniteLimits (moduleRestrictionBetweenOpens X h) := sorry

/-- Restriction between nested open subspaces preserves finite colimits. -/
theorem betweenPreservesFiniteColimits (X : RingedSpace.{u})
    {W U : Opens X.carrier} (h : W ≤ U) :
    Limits.PreservesFiniteColimits (moduleRestrictionBetweenOpens X h) := sorry

/-- Restriction between the derived categories of modules on nested open subspaces. -/
@[stacks 08DP "derived restriction between open subspaces"]
abbrev derivedBetween
    (X : RingedSpace.{u}) {W U : Opens X.carrier} (h : W ≤ U) :
    moduleDerivedOnOpen X U ⥤ moduleDerivedOnOpen X W :=
  (betweenExact X h).mapDerivedCategory

/-- Derived restriction between nested open subspaces is additive. -/
theorem derivedBetweenAdditive
    (X : RingedSpace.{u}) {W U : Opens X.carrier} (h : W ≤ U) :
    (derivedBetween X h).Additive := sorry

/-- The canonical isomorphism identifying iterated and direct derived restriction between nested
open subspaces. -/
@[stacks 08DP "composition of derived restrictions between open subspaces"]
noncomputable def derivedBetweenCompIso
    (X : RingedSpace.{u}) {T W U : Opens X.carrier} (hTW : T ≤ W) (hWU : W ≤ U) :
    derivedBetween X hWU ⋙ derivedBetween X hTW ≅
      derivedBetween X (hTW.trans hWU) :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (betweenExact X hWU) (betweenExact X hTW)).symm ≪≫
    ExactFunctor.MapDerivedCategory.mapIso
      (ObjectProperty.isoMk (exactFunctor _ _) (betweenCompIso X hTW hWU))

/-- The canonical isomorphism identifying direct derived restriction from `X` with iterated
restriction through an intermediate open. -/
@[stacks 08DP "composition of derived restriction from the ambient space"]
noncomputable def derivedCompIso
    (X : RingedSpace.{u}) {W U : Opens X.carrier} (h : W ≤ U) :
    moduleRestrictionToOpenDerived X U ⋙ derivedBetween X h ≅
      moduleRestrictionToOpenDerived X W :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (exact X U) (betweenExact X h)).symm ≪≫
    ExactFunctor.MapDerivedCategory.mapIso
      (ObjectProperty.isoMk (exactFunctor _ _) (compIso X h))

/-- The total derived pullback along the open immersion associated to an open subspace. -/
noncomputable abbrev derivedPullback
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    RingedSpace.ModuleDerived X ⥤ moduleDerivedOnOpen X U :=
  @RingedSpace.modulePullbackDerived _ _ (X.ofRestrict U.isOpenEmbedding)
    _ _ (additive X U)
    (@RingedSpace.modulePullbackToDerived_hasLeftDerivedFunctor _ _
      (X.ofRestrict U.isOpenEmbedding) _ _ (additive X U))

/-- The canonical comparison from exact restriction to an open subspace to total derived
pullback along its open immersion. -/
noncomputable def derivedPullbackComparison
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (exact X U).mapDerivedCategory ⟶
      derivedPullback X U :=
  @ExactFunctor.LeftDerived.comparison
    (RingedSpace.Modules X) _ _ _ (openSubspaceModuleCategory X U) _ _ _
    (exact X U)
    (derivedPullback X U)
    ((@RingedSpace.modulePullbackToDerived _ _ (X.ofRestrict U.isOpenEmbedding)
      (additive X U)).totalLeftDerivedCounit DerivedCategory.Qh
        (RingedSpace.ModuleQis X))
    (inferInstanceAs
      (((@RingedSpace.modulePullbackToDerived _ _
        (X.ofRestrict U.isOpenEmbedding) (additive X U)).totalLeftDerived
          DerivedCategory.Qh (RingedSpace.ModuleQis X)).IsLeftDerivedFunctor
        ((@RingedSpace.modulePullbackToDerived _ _
          (X.ofRestrict U.isOpenEmbedding) (additive X U)).totalLeftDerivedCounit
            DerivedCategory.Qh (RingedSpace.ModuleQis X))
        (RingedSpace.ModuleQis X)))

/-- Exact restriction to an open subspace and total derived pullback along its open immersion
are canonically isomorphic. -/
theorem derivedPullbackComparison_isIso
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    IsIso (derivedPullbackComparison X U) := sorry

/-- Restriction to an open subspace commutes canonically with derived-category homology. -/
noncomputable def derivedPullbackHomologyIso
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    (K : RingedSpace.ModuleDerived X) (q : ℤ) :
    (RingedSpace.Hom.pullback (X.ofRestrict U.isOpenEmbedding)).obj
        ((DerivedCategory.homologyFunctor X.Modules q).obj K) ≅
      (DerivedCategory.homologyFunctor (openSubspaceModuleCategory X U) q).obj
        ((derivedPullback X U).obj K) :=
  ((exact X U).homologyIso K q).symm ≪≫
    (DerivedCategory.homologyFunctor (openSubspaceModuleCategory X U) q).mapIso
        ((@asIso _ _ _ _ (derivedPullbackComparison X U)
          (derivedPullbackComparison_isIso X U)).app K)

end OpenSubspace.Restriction

/-- The representative obtained by restricting a chosen cochain-complex preimage of a derived
module to the open subspace `U`. -/
abbrev restrictedModuleDerivedOnOpen
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    (K : DerivedCategory (RingedSpace.Modules X)) :
    moduleDerivedOnOpen X U :=
  DerivedCategory.Q.obj
    ((moduleRestrictionComplexToOpen X U).obj (DerivedCategory.Q.objPreimage K))

/-- The canonical comparison from derived restriction of an arbitrary object to its restricted
chosen-complex representative. -/
@[stacks 0D5V "derived restriction and intrinsic open representative"]
noncomputable def OpenSubspace.Restriction.derivedObjIsoRestricted
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    (K : DerivedCategory (RingedSpace.Modules X)) :
    (moduleRestrictionToOpenDerived X U).obj K ≅ restrictedModuleDerivedOnOpen X U K :=
  (moduleRestrictionToOpenDerived X U).mapIso (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
    moduleRestrictionToOpenDerivedFactors X U (DerivedCategory.Q.objPreimage K)

/-- Restriction of a K-injective complex of `𝒪_X`-modules to an open subspace
remains K-injective. -/
@[stacks 08DP "restriction to an open preserves K-injectives"]
theorem moduleRestrictionToOpen_isKInjective
    {X : RingedSpace.{u}} (U : Opens X.carrier)
    (I : CochainComplex (Modules X) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((moduleRestrictionToOpen X U).mapHomologicalComplex (up ℤ)).obj I) := sorry

end AlgebraicGeometry.RingedSpace
