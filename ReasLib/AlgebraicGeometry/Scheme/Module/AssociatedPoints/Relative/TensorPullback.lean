/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}

namespace relativeAssassin

/-- Fiberwise associated points of a quasi-coherent scheme module flat over the base, lying over
associated points of a quasi-coherent base module, are associated points of the tensor product
with its pullback. -/
theorem inter_preimage_subset_associatedPoints_tensor_pullback
    (f : X ⟶ S) (ℱ : X.Modules) (𝒢 : S.Modules)
    [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
    (hflat : flatOver ℱ f) :
    relativeAssassin f ℱ ∩ f.base ⁻¹' associatedPoints 𝒢 ⊆
      associatedPoints (ℱ ⊗ (Scheme.Modules.pullback f).obj 𝒢) := sorry

/-- Over a locally Noetherian base, the associated points of the tensor product of a
quasi-coherent scheme module flat over the base with the pullback of a quasi-coherent base
module are exactly the fiberwise associated points lying over associated points of the base
module. -/
theorem associatedPoints_tensor_pullback_eq_inter_preimage
    (f : X ⟶ S) (ℱ : X.Modules) (𝒢 : S.Modules)
    [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
    (hflat : flatOver ℱ f) [IsLocallyNoetherian S] :
    associatedPoints (ℱ ⊗ (Scheme.Modules.pullback f).obj 𝒢) =
      relativeAssassin f ℱ ∩ f.base ⁻¹' associatedPoints 𝒢 := sorry

end relativeAssassin

end AlgebraicGeometry.Scheme.Modules
