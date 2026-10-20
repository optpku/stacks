/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import ReasLib.Algebra.Homology.DerivedCategory.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.ExtensionByZero.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived extension by zero on an open subspace

This leaf promotes the exact underived extension-by-zero owner to the unbounded derived category.
-/

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The derived extension-by-zero functor `j_! : D(𝒪_U) ⥤ D(𝒪_X)` for an open immersion
`j : U ↪ X`. -/
noncomputable abbrev moduleExtensionByZeroFromOpenDerived
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    DerivedCategory (openSubspaceModuleCategory X U) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  (moduleExtensionByZeroFromOpen X U).mapDerivedCategory

namespace OpenSubspace.ExtensionByZero

/-- The adjunction `j_! ⊣ j^*` for an open subspace descends to unbounded derived categories. -/
@[stacks 08BT "derived extension-restriction adjunction for an open immersion"]
noncomputable def derivedAdjunction
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    moduleExtensionByZeroFromOpenDerived X U ⊣ moduleRestrictionToOpenDerived X U :=
  CategoryTheory.Adjunction.mapDerivedCategory
    (adjunction X U)

/-- Derived extension by zero from an open subspace is a left adjoint. -/
instance derivedIsLeftAdjoint
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    Functor.IsLeftAdjoint (moduleExtensionByZeroFromOpenDerived X U) := sorry

/-- Derived restriction to an open subspace is a right adjoint. -/
instance derivedIsRightAdjoint
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    Functor.IsRightAdjoint (moduleRestrictionToOpenDerived X U) := sorry

/-- The unit of the derived extension-restriction adjunction is an isomorphism. -/
instance derivedUnitIsIso
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    IsIso (derivedAdjunction X U).unit := sorry

/-- Every component of the unit of the derived extension-restriction adjunction is an
isomorphism. -/
@[stacks 08BT "derived extension-restriction unit component"]
instance derivedUnitAppIsIso
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})]
    (F : moduleDerivedOnOpen X U) :
    IsIso ((derivedAdjunction X U).unit.app F) := sorry

/-- Derived extension by zero from an open subspace is fully faithful. -/
noncomputable def derivedFullyFaithful
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    (moduleExtensionByZeroFromOpenDerived X U).FullyFaithful :=
  (derivedAdjunction X U).fullyFaithfulLOfIsIsoUnit

/-- Derived extension by zero from an open subspace is full. -/
noncomputable instance derivedFull
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    (moduleExtensionByZeroFromOpenDerived X U).Full := sorry

/-- Derived extension by zero from an open subspace is faithful. -/
noncomputable instance derivedFaithful
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    (moduleExtensionByZeroFromOpenDerived X U).Faithful := sorry

end OpenSubspace.ExtensionByZero

end AlgebraicGeometry.RingedSpace
