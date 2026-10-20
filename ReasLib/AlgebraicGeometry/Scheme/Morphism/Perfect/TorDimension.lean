/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.RelativeRestriction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Local
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent
public import ReasLib.RingTheory.RingHom.Perfect.TorDimension

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.PseudoCoherent

/-- For a pseudo-coherent morphism of schemes, perfectness, local finite Tor dimension of
the derived structure sheaf over the inverse-image structure sheaf, and finite Tor dimension
of every stalk map are equivalent. -/
theorem perfect_tfae {X S : Scheme.{u}} (f : X ⟶ S) [PseudoCoherent f]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
    :
    List.TFAE [LocallyOfType RingHom.IsPerfectRingMap f,
      RingedSpace.ModuleDerived.LocallyHasFiniteTorDimension
        (X := RingedSpace.Hom.inverseImageBase f.toShHom)
        ((RingedSpace.ModuleDerived.relativeRestriction f.toShHom).obj
          (Scheme.DerivedQCoh.structureSheaf X).obj),
      ∀ x : X, (f.stalkMap x).hom.HasFiniteTorDimension] := sorry

end AlgebraicGeometry.PseudoCoherent
