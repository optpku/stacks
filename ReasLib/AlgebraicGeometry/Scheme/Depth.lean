module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth

/-!
# Depth and Serre conditions for locally Noetherian schemes

This leaf owns the structure-sheaf specialization of the coherent scheme-module
depth API. The direct stalk formulas remain available for source-facing uses,
while the comparison lemmas connect them to the module-level predicates.
-/

@[expose] public section

open AlgebraicGeometry
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- A locally Noetherian scheme has depth `k` at `x` when the local ring at `x` has depth `k`
as a module over itself. -/
abbrev hasDepthAt (x : X) (k : ℕ) : Prop :=
  moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x) = k

/-- The scheme depth-at-a-point predicate unfolds to the depth of the local ring. -/
theorem hasDepthAt_def (x : X) (k : ℕ) :
    hasDepthAt X x k =
      (moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x) = k) := sorry

/-- The scheme depth-at-a-point predicate is equivalent to the corresponding local-ring depth
equality. -/
@[simp]
theorem hasDepthAt_iff (x : X) (k : ℕ) :
    hasDepthAt X x k ↔
      moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x) = k := sorry

/-- A locally Noetherian scheme satisfies `(S_k)` when every local ring has the required depth
lower bound. -/
abbrev satisfiesSerreConditionS (k : ℕ) : Prop :=
  ∀ x : X,
    WithBot.some (moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x) : ℕ∞) ≥
      min (k : WithBot ℕ∞) (Module.supportDim (X.presheaf.stalk x) (X.presheaf.stalk x))

/-- The scheme Serre condition unfolds to its local-ring depth inequalities. -/
theorem satisfiesSerreConditionS_def (k : ℕ) :
    satisfiesSerreConditionS X k =
      (∀ x : X,
        WithBot.some (moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x) : ℕ∞) ≥
          min (k : WithBot ℕ∞)
            (Module.supportDim (X.presheaf.stalk x) (X.presheaf.stalk x))) := sorry

/-- The scheme Serre condition is equivalent to its local-ring depth inequalities. -/
@[simp]
theorem satisfiesSerreConditionS_iff (k : ℕ) :
    satisfiesSerreConditionS X k ↔
      ∀ x : X,
        WithBot.some (moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x) : ℕ∞) ≥
          min (k : WithBot ℕ∞)
            (Module.supportDim (X.presheaf.stalk x) (X.presheaf.stalk x)) := sorry

/-- The scheme Serre condition is equivalent to the stalkwise depth bound expressed using the
Krull dimension of each local ring. -/
theorem satisfiesSerreConditionS_iff_ringKrullDim (k : ℕ) :
    satisfiesSerreConditionS X k ↔
      ∀ x : X,
        WithBot.some (moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x) : ℕ∞) ≥
          min (k : WithBot ℕ∞) (ringKrullDim (X.presheaf.stalk x)) := sorry

/-- Scheme depth is the coherent-module depth predicate applied to the structure module. -/
theorem hasDepthAt_iff_structureSheaf (x : X) (k : ℕ) :
    hasDepthAt X x k ↔
      Scheme.Modules.hasDepthAt
        (ℱ := (SheafOfModules.unit X.ringCatSheaf : X.Modules)) x k := sorry

/-- Scheme Serre's condition is the coherent-module Serre condition applied to the structure
module. -/
theorem satisfiesSerreConditionS_iff_structureSheaf (k : ℕ) :
    satisfiesSerreConditionS X k ↔
      Scheme.Modules.satisfiesSerreConditionS
        (ℱ := (SheafOfModules.unit X.ringCatSheaf : X.Modules)) k := sorry

end AlgebraicGeometry.Scheme
