/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.Galois.Notation
public import ReasLib.FieldTheory.TensorProduct.Branch
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAction
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.IntegralClosure
public import ReasLib.RingTheory.Invariant.Quotient
import Mathlib.Tactic.CrossRefAttribute

/-!
# Galois actions on reduced tensor base changes

The right-factor action on `L ⊗[K] K₁` descends through the nilradical.  For a finite normal
extension `K₁ / K`, the induced action on the integral closure over a DVR is transitive on maximal
ideals.

@stack 09EU
-/

@[expose] public section

open Ideal
open scoped Algebra.TensorProduct.RightAction Pointwise TensorProduct

universe u v w x y

noncomputable section

namespace FieldExtension.TensorProduct.RightGalois

/-- The nilradical of a field tensor product is stable under the action through its right
factor. -/
@[stacks 09EU "nilradical stability under the right-factor Galois action"]
theorem nilradicalStable
    (K : Type w) (L : Type x) (K1 : Type y)
    [Field K] [Field L] [Algebra K L] [Field K1] [Algebra K K1] :
    -- Local instance justification (instance diamond): select the action through the right
    -- tensor factor for this stability statement.
    letI : MulSemiringAction Gal(K1/K) (baseChange K L K1) :=
      Algebra.TensorProduct.RightAction.action
    Ideal.IsStable (nilradical (baseChange K L K1)) Gal(K1/K) := sorry
-- Proof strategy: unfold ideal stability; each group element acts by the right-factor tensor ring
-- automorphism, so applying it to a nilpotence equation preserves the same vanishing power and
-- hence membership in the nilradical.

/-- The descended right-factor action on a reduced field tensor product commutes with scalars
from every ring acting through the left field factor. -/
@[stacks 09EU "scalar compatibility of the reduced right-factor action"]
theorem quotientSMulCommClass
    (B : Type v) (K : Type w) (L : Type x) (K1 : Type y)
    [CommRing B] [Field K] [Field L] [Algebra B L] [Algebra K L]
    [Field K1] [Algebra K K1] :
    let T := baseChange K L K1
    -- Local instance justification (instance diamond): select the action through the right
    -- tensor factor before descending it to the reduction.
    letI : MulSemiringAction Gal(K1/K) T := Algebra.TensorProduct.RightAction.action
    -- Local declaration justification (proof-local temporary data): quotient descent uses the
    -- stability proof for this canonical nilradical.
    let hI : Ideal.IsStable (nilradical T) Gal(K1/K) := nilradicalStable K L K1
    -- Local instance justification (defeq pin): retain the quotient action determined by `hI`.
    letI : MulSemiringAction Gal(K1/K) (T ⧸ nilradical T) := Ideal.Quotient.action _ hI
    SMulCommClass Gal(K1/K) B (T ⧸ nilradical T) := sorry
-- Proof strategy: use quotient induction on the reduced tensor element; rewrite the quotient
-- action with `Ideal.Quotient.smul_mk`, and use that the right-factor action fixes the left tensor
-- embedding of `L`, hence commutes with every scalar coming from `B`.

end FieldExtension.TensorProduct.RightGalois

namespace DVR.Field.BaseChange.Galois

variable {B : Type v} {K : Type w} {L : Type x} {K1 : Type y}
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Field K] [Field L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [Field K1] [Algebra K K1]
variable [FiniteDimensional K K1] [Normal K K1]

local notation "G" => Gal(K1 / K)
local notation "T" => FieldExtension.TensorProduct.baseChange K L K1
local notation "L₁" => FieldExtension.TensorProduct.reduced K L K1
local notation "B₁" => integralClosure B L₁

/-- Lemma 15.116.6: for a finite normal extension `K₁ / K`, the canonical `Gal(K₁/K)`-action on
`B₁ = integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))` is transitive on the maximal
ideals of `B₁`. -/
@[stacks 09EU "Galois transitivity on maximal ideals after reduced base change"]
theorem exists_smul_eq_of_isMaximal (m m' : Ideal B₁) [m.IsMaximal] [m'.IsMaximal] :
    -- Local instance justification (instance diamond): select the action through the `K₁`
    -- tensor factor.
    letI : MulSemiringAction G T := Algebra.TensorProduct.RightAction.action
    -- Local declaration justification (proof-local temporary data): the quotient action uses
    -- stability of the canonical nilradical.
    let hI : Ideal.IsStable (nilradical T) G :=
      FieldExtension.TensorProduct.RightGalois.nilradicalStable K L K1
    -- Local instance justification (defeq pin): the reduction uses the action determined by
    -- `hI`.
    letI : MulSemiringAction G L₁ := Ideal.Quotient.action _ hI
    -- Local instance justification (defeq pin): the integral-closure action uses the same
    -- reduced-ring action and scalar compatibility.
    letI : SMulCommClass G B L₁ :=
      FieldExtension.TensorProduct.RightGalois.quotientSMulCommClass B K L K1
    -- Local instance justification (defeq pin): select Mathlib's induced integral-closure
    -- action over the preceding reduced-ring action.
    letI : MulSemiringAction G B₁ := inferInstance
    ∃ σ : G, σ • m = m' := sorry
-- Proof strategy: argue by contradiction and use the invariant-quotient conjugacy theorem to
-- produce a fixed element lying in `m` but not `m'`.  Descend a positive power of that element
-- through the fixed field `K1 ^ G = K` to an element of the base DVR `B`; both maximal ideals
-- contract to `maximalIdeal B`, contradicting the separating memberships.

end DVR.Field.BaseChange.Galois
