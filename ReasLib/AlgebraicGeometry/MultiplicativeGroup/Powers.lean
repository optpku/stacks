module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import ReasLib.AlgebraicGeometry.MultiplicativeGroup
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Finite powers of the multiplicative group scheme
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.MultiplicativeGroup
open MonoidalCategory CartesianMonoidalCategory
open scoped AlgebraicGeometry CategoryTheory MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.MultiplicativeGroup

/-- The `n`-fold cartesian product of the multiplicative group scheme over `k`. -/
def pow (k : Type u) [Field k] : ℕ → SchemeOverField k
  | 0 => 𝟙_ (SchemeOverField k)
  | n + 1 => (𝔾ₘ[Spec (CommRingCat.of k)]).X ⊗ pow k n

/-- The empty product of multiplicative groups is the monoidal unit over `Spec k`. -/
theorem pow_zero (k : Type u) [Field k] :
    pow k 0 = 𝟙_ (SchemeOverField k) := sorry

/-- The successor product adjoins one more copy of the multiplicative group. -/
theorem pow_succ (k : Type u) [Field k] (n : ℕ) :
    pow k (n + 1) = (𝔾ₘ[Spec (CommRingCat.of k)]).X ⊗ pow k n := sorry

/-- The `n`-fold product of the multiplicative group over `k` is a group object. -/
instance instGrpObjPow (k : Type u) [Field k] : (n : ℕ) → GrpObj (pow k n)
  | 0 => GrpObj.instTensorUnit
  | n + 1 =>
    @GrpObj.tensorObj.instTensorObj (SchemeOverField k) _ _ _
      (𝔾ₘ[Spec (CommRingCat.of k)]).X (pow k n) _ (instGrpObjPow k n)

end AlgebraicGeometry.MultiplicativeGroup
