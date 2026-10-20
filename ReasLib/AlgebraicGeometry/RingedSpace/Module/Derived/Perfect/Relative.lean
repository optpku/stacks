/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.RelativeRestriction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Local
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice

@[expose] public section

/-!
# Relative perfectness on ringed spaces

A derived `𝒪_X`-module is perfect over a morphism `f : X ⟶ S` when it is pseudo-coherent
over `𝒪_X` and its restriction to `f⁻¹𝒪_S` locally has finite Tor dimension.
-/

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X S : RingedSpace.{u}}

/-- The object property of being pseudo-coherent over `𝒪_X` and locally of finite Tor
dimension after restriction to `f⁻¹𝒪_S`. -/
def perfectOver (f : X ⟶ S)
   [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f).carrier,
    DerivedCategory.DerivedTensor.Right.Has
      (C := RingedSpace.Modules ((RingedSpace.Hom.inverseImageBase f).restrict U.isOpenEmbedding))] : ObjectProperty (ModuleDerived X) :=
  (fun E ↦ IsPseudoCoherent E) ⊓
    (locallyFiniteTorDimension (X := RingedSpace.Hom.inverseImageBase f)).inverseImage
      (relativeRestriction f)

/-- Object-level membership in the relative-perfect object property. -/
abbrev IsPerfectOver (f : X ⟶ S)
   [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f).carrier,
    DerivedCategory.DerivedTensor.Right.Has
      (C := RingedSpace.Modules ((RingedSpace.Hom.inverseImageBase f).restrict U.isOpenEmbedding))] (E : ModuleDerived X) : Prop :=
  perfectOver f E

/-- Relative perfectness consists exactly of pseudo-coherence over `𝒪_X` and local finite Tor
dimension after restriction to `f⁻¹𝒪_S`. -/
theorem isPerfectOver_iff (f : X ⟶ S)
   [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f).carrier,
    DerivedCategory.DerivedTensor.Right.Has
      (C := RingedSpace.Modules ((RingedSpace.Hom.inverseImageBase f).restrict U.isOpenEmbedding))] (E : ModuleDerived X) :
    IsPerfectOver f E ↔
      IsPseudoCoherent E ∧
        LocallyHasFiniteTorDimension (X := RingedSpace.Hom.inverseImageBase f)
          ((relativeRestriction f).obj E) := sorry

namespace IsPerfectOver

/-- The pseudo-coherent component of relative perfectness. -/
theorem isPseudoCoherent {f : X ⟶ S}
   [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f).carrier,
    DerivedCategory.DerivedTensor.Right.Has
      (C := RingedSpace.Modules ((RingedSpace.Hom.inverseImageBase f).restrict U.isOpenEmbedding))] {E : ModuleDerived X}
    (hE : IsPerfectOver f E) : IsPseudoCoherent E := sorry

/-- The local finite-Tor-dimension component of relative perfectness. -/
theorem locallyHasFiniteTorDimension {f : X ⟶ S}
   [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f).carrier,
    DerivedCategory.DerivedTensor.Right.Has
      (C := RingedSpace.Modules ((RingedSpace.Hom.inverseImageBase f).restrict U.isOpenEmbedding))] {E : ModuleDerived X}
    (hE : IsPerfectOver f E) :
    LocallyHasFiniteTorDimension (X := RingedSpace.Hom.inverseImageBase f)
          ((relativeRestriction f).obj E) := sorry

end IsPerfectOver

/-- Relative perfectness is invariant under isomorphisms of derived modules. -/
instance perfectOver_isClosedUnderIsomorphisms (f : X ⟶ S)
   [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f).carrier,
    DerivedCategory.DerivedTensor.Right.Has
      (C := RingedSpace.Modules ((RingedSpace.Hom.inverseImageBase f).restrict U.isOpenEmbedding))] :
    (perfectOver f).IsClosedUnderIsomorphisms := sorry

namespace IsPerfectOver

/-- Transport relative perfectness across an isomorphism of derived modules. -/
theorem ofIso {f : X ⟶ S}
   [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f).carrier,
    DerivedCategory.DerivedTensor.Right.Has
      (C := RingedSpace.Modules ((RingedSpace.Hom.inverseImageBase f).restrict U.isOpenEmbedding))] {E E' : ModuleDerived X}
    (hE : IsPerfectOver f E) (e : E ≅ E') : IsPerfectOver f E' := sorry

end IsPerfectOver

end AlgebraicGeometry.RingedSpace.ModuleDerived
