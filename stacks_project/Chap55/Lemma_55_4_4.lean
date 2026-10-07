module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.PicardContraction

@[expose] public section

namespace NumericalType

/- Lemma 55.4.4
   For a numerical type `T` with a chosen `(-1)`-index, contraction induces an
   injective map on Picard groups whose cokernel is annihilated by two. -/
@[stacks 0C7J] #check
  (NumericalType.exists_picardGroup_contractMinusOne_injective :
    ∀ (T : NumericalType)
      (e : Fin (T.n - 1 + 1) ≃ Fin T.n)
      (hminus : NumericalType.IsMinusOneIndex T.componentGenus T.weight
        T.intersection (e (Fin.last (T.n - 1)))),
      ∃ φ : T.PicardGroup →ₗ[ℤ]
          (NumericalType.contractMinusOne T e hminus).PicardGroup,
        Function.Injective φ ∧
          ∀ x :
              ((NumericalType.contractMinusOne T e hminus).PicardGroup ⧸
                LinearMap.range φ),
            x + x = 0)

end NumericalType
