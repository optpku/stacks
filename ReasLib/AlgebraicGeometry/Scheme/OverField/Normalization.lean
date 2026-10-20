module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local
public import ReasLib.RingTheory.Normal.Nagata
public import ReasLib.RingTheory.Normalization.Basic

/-!
# Normalization Invariants of Schemes over a Field

This leaf provides pointwise normalization invariants by applying the
ring-theoretic construction to scheme stalks.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

noncomputable section

variable {k : Type u} [Field k]

/-- A stalk of a locally algebraic scheme over a field is a Nagata local ring. -/
@[instance]
instance instNagataRingStalkOfLocallyAlgebraic
    (X : Over (Spec (CommRingCat.of k))) [LocallyAlgebraic X] (x : X.left) :
    NagataRing (stalkRing X x) := sorry

/-- The pointwise `δ`-invariant of a scheme over a field is
the normalization `δ`-invariant of its stalk. -/
@[stacks 0C1T]
noncomputable def deltaInvariantAt
    (X : Over (Spec (CommRingCat.of k))) (x : X.left) : ℕ∞ :=
  Normalization.deltaInvariant (stalkRing X x)

/-- The pointwise `δ`-invariant of a scheme over a field is the normalization
`δ`-invariant of its stalk. -/
@[simp]
theorem deltaInvariantAt_def (X : Over (Spec (CommRingCat.of k))) (x : X.left) :
    deltaInvariantAt X x = Normalization.deltaInvariant (stalkRing X x) := sorry

end

end AlgebraicGeometry.SchemeOverField
