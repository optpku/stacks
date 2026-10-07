module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Depth
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Serre's conditions for schemes

For a scheme, condition `(R_k)` means regularity at every point whose local ring has Krull
dimension at most `k`. The scheme-level `(S_k)` API is re-exported from `Scheme.Depth`.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- A scheme is regular in codimension `k`, or satisfies `(R_k)`, if every stalk of Krull
dimension at most `k` is a regular local ring. -/
@[stacks 033Q]
def satisfiesSerreConditionR (k : ℕ) : Prop :=
  ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ k → IsRegularLocalRing (X.presheaf.stalk x)

/-- Unfold the stalkwise `(R_k)` condition for a scheme. -/
@[simp] theorem satisfiesSerreConditionR_iff (k : ℕ) :
    satisfiesSerreConditionR X k ↔
      ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ k → IsRegularLocalRing (X.presheaf.stalk x) :=
  Iff.rfl

/-- If a scheme satisfies `(R_k)`, then each stalk of Krull dimension at most `k` is a regular
local ring. -/
theorem satisfiesSerreConditionR.isRegularLocalRing_stalk {X : Scheme.{u}} {k : ℕ}
    (hX : satisfiesSerreConditionR X k) (x : X)
    (hx : ringKrullDim (X.presheaf.stalk x) ≤ k) :
    IsRegularLocalRing (X.presheaf.stalk x) :=
  hX x hx

/-- On a locally Noetherian scheme, `(R_k)` implies the ring-level Serre condition `(R_k)` on
every stalk. -/
theorem satisfiesSerreConditionR.serreConditionR_stalk {X : Scheme.{u}} {k : ℕ}
    [IsLocallyNoetherian X]
    (hX : satisfiesSerreConditionR X k) (x : X) :
    SerreConditionR (X.presheaf.stalk x) k := by
  sorry

/-- On a locally Noetherian scheme, stalkwise ring-level `(R_k)` implies the scheme condition
`(R_k)`. -/
theorem satisfiesSerreConditionR.of_stalkwise_serreConditionR {X : Scheme.{u}} {k : ℕ}
    [IsLocallyNoetherian X]
    (hX : ∀ x : X, SerreConditionR (X.presheaf.stalk x) k) :
    satisfiesSerreConditionR X k := by
  intro x hx
  let A := X.presheaf.stalk x
  -- Local instance justification (proof-local temporary data): install the explicit stalkwise proof only to invoke the ring-level class API.
  letI : SerreConditionR A k := hX x
  exact SerreConditionR.isRegularLocalRing_of_ringKrullDim_le A hx

/-- On a locally Noetherian scheme, `(R_k)` is equivalent to requiring every stalk to satisfy the
ring-level Serre condition `(R_k)`. -/
theorem satisfiesSerreConditionR_iff_stalkwise_serreConditionR
    [IsLocallyNoetherian X] (k : ℕ) :
    satisfiesSerreConditionR X k ↔ ∀ x : X, SerreConditionR (X.presheaf.stalk x) k := by
  constructor
  · intro hX x
    exact satisfiesSerreConditionR.serreConditionR_stalk hX x
  · intro hX
    exact satisfiesSerreConditionR.of_stalkwise_serreConditionR hX

end AlgebraicGeometry.Scheme
