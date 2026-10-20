/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.GlobalSections

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped CartesianClosed CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- If a separated, finitely presented, flat scheme morphism has affine base and
`RΓ(X, E ⊗ᴸ K)` is perfect for every perfect `E`, then `K` is perfect over the base. -/
theorem isPerfectOver_of_globalSectionsTensor
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f]
    [Scheme.Hom.FinitePresentation f] [Flat f]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)] (K : DerivedQCoh X)
    (hperfect : ∀ E : RingedSpace.ModuleDerived X.toRingedSpace,
      RingedSpace.ModuleDerived.IsPerfect E →
        DerivedCategory.IsPerfect
          ((Scheme.FlatPullbackSections.baseSections f).obj (E ⊗ᴸ K.obj))) :
    RingedSpace.ModuleDerived.IsPerfectOver f.toShHom K.obj := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
