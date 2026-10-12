/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType.Minimality

@[expose] public section

namespace NumericalType

#check (NumericalType.IsMinimal : NumericalType → Prop)

#check (NumericalType.isMinimal_iff :
  ∀ (T : NumericalType),
    T.IsMinimal ↔
      ¬ ∃ i, T.componentGenus i = 0 ∧ T.intersection i i = -(T.weight i : ℤ))

#check (NumericalType.IsMinimal.not_isMinusOneIndex :
  ∀ {T : NumericalType}, T.IsMinimal → ∀ i : Fin T.n,
    ¬ NumericalType.IsMinusOneIndex T.componentGenus T.weight T.intersection i)

#check (NumericalType.IsRelabeling.isMinimal_iff :
  ∀ {T T' : NumericalType} {e : Fin T.n ≃ Fin T'.n},
    NumericalType.IsRelabeling T T' e → (T.IsMinimal ↔ T'.IsMinimal))

end NumericalType
