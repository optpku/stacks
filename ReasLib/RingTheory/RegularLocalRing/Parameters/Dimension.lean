/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RegularLocalRing.Parameters

@[expose] public section

/-!
# Dimension of Parameter-Ideal Quotients

@stack 02IE

The central theorem is stated for a system of parameters in an arbitrary
Noetherian local ring.  Regular-local consequences are deliberately left to
`Parameters.Properties` so this leaf remains the reusable dimension owner.
-/

universe u

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

namespace IsSystemOfParameters

/-- Lemma 10.60.14, tag `02IE`: quotienting by the parameter ideal of the
first `i` entries of a system of parameters leaves Krull dimension `d - i`. -/
@[stacks 02IE]
theorem ringKrullDim_quotient_parameterIdeal_eq_sub
    {d i : ℕ} {x : Fin d → maximalIdeal R}
    (hx : IsSystemOfParameters x) (hi : i ≤ d) :
    ringKrullDim (R ⧸ parameterIdeal (x ∘ Fin.castLE hi)) = d - i := sorry

/-- The dimension formula for a parameter-ideal prefix in additive form. -/
@[stacks 02IE]
theorem ringKrullDim_quotient_parameterIdeal_add_length_eq
    {d i : ℕ} {x : Fin d → maximalIdeal R}
    (hx : IsSystemOfParameters x) (hi : i ≤ d) :
    ringKrullDim (R ⧸ parameterIdeal (x ∘ Fin.castLE hi)) + i = ringKrullDim R := sorry

end IsSystemOfParameters

namespace IsPartOfRegularSystemOfParameters

/-- A partial regular system cuts out a quotient whose Krull dimension is the
length of its ambient completion minus the length of the partial family. -/
@[stacks 02IE]
theorem ringKrullDim_quotient_parameterIdeal_eq_sub
    {d c : ℕ} {x : Fin c → maximalIdeal R}
    (hx : IsPartOfRegularSystemOfParameters d x) :
    ringKrullDim (R ⧸ parameterIdeal x) = d - c := sorry

/-- A partial regular system lowers Krull dimension by the number of its
entries. -/
@[stacks 02IE]
theorem ringKrullDim_quotient_parameterIdeal_add_length_eq
    {d c : ℕ} {x : Fin c → maximalIdeal R}
    (hx : IsPartOfRegularSystemOfParameters d x) :
    ringKrullDim (R ⧸ parameterIdeal x) + c = ringKrullDim R := sorry

end IsPartOfRegularSystemOfParameters

/-- Lemma 10.60.14, tag `02IE`, unbundled form: if a finite family generates
an ideal of definition and has length equal to the Krull dimension, quotienting
by an initial segment lowers the dimension by the segment length. -/
@[stacks 02IE]
theorem ringKrullDim_quotient_initialSegmentIdeal_eq_sub
    {d i : ℕ} (x : Fin d → R)
    (hdef : Ideal.IsIdealOfDefinition (Ideal.span (Set.range x)))
    (hdim : ringKrullDim R = d) (hi : i ≤ d) :
    ringKrullDim (R ⧸ Ideal.span (Set.range (x ∘ Fin.castLE hi))) = d - i := sorry

end IsLocalRing
