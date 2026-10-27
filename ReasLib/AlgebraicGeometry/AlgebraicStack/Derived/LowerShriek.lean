/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.ModuleAbelian
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.ModuleLowerShriek
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.QuasiCoherent

/-!
# Derived module lower shriek on algebraic-stack sites

The lisse-étale and flat-fppf inclusions induce total left-derived lower-shriek
functors, with degree-zero inputs and integer-degree cohomology objects.

The modules here have coefficient universe `u`, whereas the underlying sites
have object universe `u + 1`. The generic ringed-site derived lower-shriek
construction uses section-universe bounds on the site categories; it therefore
does not directly specialize to this smaller-coefficient convention. These
functors use the standard derived categories of the smaller module categories
and the total left-derived construction on their homotopy categories.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.GroupoidsOver CategoryTheory
open ComplexShape RingedSite.Cocontinuous

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- The standard derived-category structure on lisse-étale `𝒪`-modules. -/
instance lisseEtaleModules_hasDerivedCategory (X : GroupoidsOver S)
    [AlgebraicStack X] :
    HasDerivedCategory (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) :=
  HasDerivedCategory.standard (SheafOfModules.{u} (lisseEtaleStructureSheaf X))

/-- The standard derived-category structure on flat-fppf `𝒪`-modules. -/
instance flatFppfModules_hasDerivedCategory (X : GroupoidsOver S)
    [AlgebraicStack X] :
    HasDerivedCategory (SheafOfModules.{u} (flatFppfStructureSheaf X)) :=
  HasDerivedCategory.standard (SheafOfModules.{u} (flatFppfStructureSheaf X))

/-- Lisse-étale module lower shriek is additive. -/
instance lisseEtaleModuleLowerShriek.instAdditive (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (lisseEtaleModuleLowerShriek X).Additive :=
  moduleLowerShriek.additive (lisseEtaleInclusion X) (etaleStructureSheaf X)

/-- Flat-fppf module lower shriek is additive. -/
instance flatFppfModuleLowerShriek.instAdditive (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (flatFppfModuleLowerShriek X).Additive :=
  moduleLowerShriek.additive (flatFppfInclusion X) (structureSheaf X)

namespace lisseEtaleModuleLowerShriek

/-- Homotopy-to-derived presentation of lisse-étale module lower shriek. -/
abbrev toDerived (X : GroupoidsOver S) [AlgebraicStack X] :
    HomotopyCategory (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) (up ℤ) ⥤
      ModuleDerivedEtale X :=
  (lisseEtaleModuleLowerShriek X).mapHomotopyCategory (up ℤ) ⋙
    DerivedCategory.Qh

/-- The homotopy-to-derived lisse-étale module lower shriek has a total left
derived functor. -/
instance toDerived.hasLeftDerived (X : GroupoidsOver S) [AlgebraicStack X] :
    Functor.HasLeftDerivedFunctor (toDerived X)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) (up ℤ)) :=
  sorry

/-- Derived module lower shriek from the lisse-étale site to
`D(X_étale, 𝒪_X)`. -/
abbrev derived (X : GroupoidsOver S) [AlgebraicStack X] :
    DerivedCategory (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) ⥤
      ModuleDerivedEtale X :=
  Functor.totalLeftDerived (toDerived X) DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) (up ℤ))

/-- `Lg_!` of a lisse-étale module, viewed as an object of `D(X_étale, 𝒪_X)`. -/
abbrev singleDerived (X : GroupoidsOver S) [AlgebraicStack X]
    (H : SheafOfModules.{u} (lisseEtaleStructureSheaf X)) :
    ModuleDerivedEtale X :=
  (derived X).obj
    ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) (0 : ℤ)).obj H)

/-- Degree-`p` cohomology of `Lg_! H` on the associated étale site. -/
abbrev homology (X : GroupoidsOver S) [AlgebraicStack X]
    (H : SheafOfModules.{u} (lisseEtaleStructureSheaf X)) (p : ℤ) :
    etaleModules X :=
  (DerivedCategory.homologyFunctor (etaleModules X) p).obj (singleDerived X H)

end lisseEtaleModuleLowerShriek

namespace flatFppfModuleLowerShriek

/-- Homotopy-to-derived presentation of flat-fppf module lower shriek. -/
abbrev toDerived (X : GroupoidsOver S) [AlgebraicStack X] :
    HomotopyCategory (SheafOfModules.{u} (flatFppfStructureSheaf X)) (up ℤ) ⥤
      ModuleDerived X :=
  (flatFppfModuleLowerShriek X).mapHomotopyCategory (up ℤ) ⋙
    DerivedCategory.Qh

/-- The homotopy-to-derived flat-fppf module lower shriek has a total left
derived functor. -/
instance toDerived.hasLeftDerived (X : GroupoidsOver S) [AlgebraicStack X] :
    Functor.HasLeftDerivedFunctor (toDerived X)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (flatFppfStructureSheaf X)) (up ℤ)) :=
  sorry

/-- Derived module lower shriek from the flat-fppf site to `D(𝒪_X)`. -/
abbrev derived (X : GroupoidsOver S) [AlgebraicStack X] :
    DerivedCategory (SheafOfModules.{u} (flatFppfStructureSheaf X)) ⥤
      ModuleDerived X :=
  Functor.totalLeftDerived (toDerived X) DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (flatFppfStructureSheaf X)) (up ℤ))

/-- `Lg_!` of a flat-fppf module, viewed as an object of `D(𝒪_X)`. -/
abbrev singleDerived (X : GroupoidsOver S) [AlgebraicStack X]
    (H : SheafOfModules.{u} (flatFppfStructureSheaf X)) :
    ModuleDerived X :=
  (derived X).obj
    ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (flatFppfStructureSheaf X)) (0 : ℤ)).obj H)

/-- Degree-`p` cohomology of `Lg_! H` on the fppf site of `X`. -/
abbrev homology (X : GroupoidsOver S) [AlgebraicStack X]
    (H : SheafOfModules.{u} (flatFppfStructureSheaf X)) (p : ℤ) :
    fppfModules X :=
  (DerivedCategory.homologyFunctor (fppfModules X) p).obj (singleDerived X H)

end flatFppfModuleLowerShriek

end AlgebraicGeometry.AlgebraicStack
