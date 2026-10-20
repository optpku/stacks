/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Perfect.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Tensor.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tensor

/-!
# Relative perfectness and derived tensor products on schemes

This file gives preservation results for perfectness relative to a flat, locally finitely
presented morphism of schemes.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.DerivedCategory.DerivedTensor

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.Scheme.ModuleDerived.IsPerfect

/-- An absolutely perfect derived module on the source of a flat, locally finitely presented
morphism of schemes is perfect relative to that morphism. -/
theorem isPerfectRelativeTo {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
    {K : RingedSpace.ModuleDerived X.toRingedSpace}
    (hK : RingedSpace.ModuleDerived.IsPerfect K) :
    Scheme.ModuleDerived.IsPerfectRelativeTo f K := sorry

/-- Tensoring a relatively perfect derived module on the left by an absolutely perfect derived
module preserves perfectness relative to a flat, locally finitely presented morphism. -/
theorem tensor_isPerfectRelativeTo {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
    {K M : RingedSpace.ModuleDerived X.toRingedSpace}
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    (hK : RingedSpace.ModuleDerived.IsPerfect K)
    (hM : Scheme.ModuleDerived.IsPerfectRelativeTo f M) :
    Scheme.ModuleDerived.IsPerfectRelativeTo f (K ⊗ᴸ M) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.IsPerfect
