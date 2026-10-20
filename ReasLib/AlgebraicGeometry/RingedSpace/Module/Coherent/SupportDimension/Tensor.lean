/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent.SupportDimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Tensor

/-!
# Tensor products of coherent modules with bounded support dimension

Tensoring a bounded coherent module by an invertible module preserves its support bound.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.CohLE

/-- Tensoring a bounded coherent module with an invertible module preserves its support
bound. -/
theorem tensorInvertible_support_le
    {X : Scheme.{u}} (d : X → ℤ) (n : ℤ) (F : CohLE X.toRingedSpace d n)
    (L : X.Modules) [Scheme.Modules.Invertible L] :
    ∀ x ∈ RingedSpace.moduleSupport (F.obj.obj ⊗ L), d x ≤ n := sorry

/-- Tensor a bounded coherent module with an invertible module, retaining the same support
bound. -/
noncomputable def tensorInvertible
    {X : Scheme.{u}} [IsLocallyNoetherian X] (d : X → ℤ) (n : ℤ)
    (F : CohLE X.toRingedSpace d n) (L : X.Modules) [Scheme.Modules.Invertible L] :
    CohLE X.toRingedSpace d n :=
  ⟨⟨F.obj.obj ⊗ L,
      @Scheme.Modules.isCoherent_tensor X F.obj.obj L inferInstance F.obj.property
        (Scheme.Modules.isCoherent_of_isInvertible L)⟩,
    (Coh.supportDimensionLE_iff d n _).2 (tensorInvertible_support_le d n F L)⟩

/-- The module underlying an invertible tensor twist is the indicated tensor product. -/
theorem tensorInvertible_obj
    {X : Scheme.{u}} [IsLocallyNoetherian X] (d : X → ℤ) (n : ℤ)
    (F : CohLE X.toRingedSpace d n) (L : X.Modules) [Scheme.Modules.Invertible L] :
    (tensorInvertible d n F L).obj.obj = F.obj.obj ⊗ L := sorry

end AlgebraicGeometry.RingedSpace.CohLE
