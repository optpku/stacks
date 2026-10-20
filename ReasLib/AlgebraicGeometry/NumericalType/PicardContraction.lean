/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType.Contraction
public import ReasLib.AlgebraicGeometry.NumericalType.Picard

@[expose] public section

namespace NumericalType

/-- A `(-1)`-index contraction induces an injective map on Picard groups whose
cokernel is annihilated by two. -/
public theorem exists_picardGroup_contractMinusOne_injective
    (T : NumericalType)
    (e : Fin (T.n - 1 + 1) ≃ Fin T.n)
    (hminus : IsMinusOneIndex T.componentGenus T.weight T.intersection
      (e (Fin.last (T.n - 1)))) :
    ∃ φ : T.PicardGroup →ₗ[ℤ] (contractMinusOne T e hminus).PicardGroup,
      Function.Injective φ ∧
        ∀ x : ((contractMinusOne T e hminus).PicardGroup ⧸ LinearMap.range φ),
          x + x = 0 := sorry

end NumericalType
