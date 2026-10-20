/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.LocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Resolution
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

/-!
# Grothendieck groups of vector bundles on schemes

This module defines the canonical comparison from the Grothendieck group of finite locally
free modules to the triangulated Grothendieck group of perfect derived modules.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The Grothendieck group of finite locally free `O_X`-modules, with relations from
ambient short exact sequences. -/
abbrev VectorBundleK0 (X : Scheme.{u}) : Type (u + 1) :=
  ObjectProperty.GrothendieckGroup
    (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)

namespace VectorBundleK0

/-- The functor sending a finite locally free `O_X`-module to its degree-zero perfect
derived realization. -/
noncomputable def toPerfect (X : Scheme.{u}) :
    ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) ⥤
      RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace) :=
  ObjectProperty.FullSubcategory.restrict
    (DerivedCategory.singleFunctor X.Modules (0 : ℤ))
    (fun E hE ↦ @SheafOfModules.IsFiniteLocallyFree.isPerfect _ E hE)

/-- The underlying derived object of `toPerfect X` is the degree-zero realization. -/
theorem toPerfect_obj (X : Scheme.{u})
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    ((toPerfect X).obj E).obj =
      (DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj E.obj := sorry

/-- The degree-zero perfect-derived class kills the short-exact relations defining
`VectorBundleK0 X`. -/
theorem relations_le_ker_toK0 (X : Scheme.{u}) :
    ObjectProperty.GrothendieckGroup.relations
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) ≤
      (FreeAbelianGroup.lift (fun E :
          ObjectProperty.FullSubcategory
            (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) ↦
        TriangulatedK0.of ((toPerfect X).obj E))).ker := sorry

/-- The comparison homomorphism from vector-bundle `K₀` to perfect-derived `K₀`. -/
noncomputable def toK0 (X : Scheme.{u}) : VectorBundleK0 X →+ K0 X :=
  ObjectProperty.GrothendieckGroup.lift
    (fun E ↦ TriangulatedK0.of ((toPerfect X).obj E))
    (relations_le_ker_toK0 X)

/-- The comparison map sends a vector-bundle generator to its degree-zero
perfect-derived class. -/
theorem toK0_of (X : Scheme.{u})
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    toK0 X (ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E) =
      TriangulatedK0.of ((toPerfect X).obj E) := sorry

/-- On a quasi-compact, quasi-separated scheme with the resolution property, the canonical
comparison from vector-bundle `K₀` to perfect-derived `K₀` is bijective. -/
theorem toK0_bijective {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (hX : HasResolutionProperty X) : Function.Bijective (toK0 X) := sorry

end VectorBundleK0

end AlgebraicGeometry.Scheme
