module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.BaseChange.Normalization
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.FormalSmooth
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Formal smoothness after finite DVR base change

This leaf owns the source-facing branch statement for the current Stacks Lemma 15.116.3.  The
reduced tensor product and integral-closure comparison map are imported from the generic
`integralClosure.BaseChange` owner; no Chapter 15 implementation is imported here.

@stack 09EQ
-/

open IsLocalRing
open scoped TensorProduct

universe u v w x y

namespace DVR.Field.BaseChange

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing B L]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]
variable [FiniteDimensional K K1]

local notation "A₁" => integralClosure A K1
local notation "L₁" => FieldExtension.TensorProduct.reduced K L K1
local notation "B₁" => integralClosure B L₁

/-- Lemma 15.115.3 (09EQ): if `A → B` is formally smooth for the maximal-ideal-adic
topology, then every localized branch `(A₁)ₘ → (B₁)ₙ` after finite base change is formally
smooth for the maximal-ideal-adic topology on `(B₁)ₙ`. -/
@[stacks 09EQ "formal smoothness after finite DVR base change"]
theorem formallySmoothAt
    (hfs : (algebraMap A B).formally_smooth_for_adic (maximalIdeal B))
    (m : Ideal A₁) [m.IsMaximal]
    (n : Ideal B₁) [n.IsMaximal] [n.LiesOver m] :
    -- Local instance justification (defeq pin): use the `CommRing` model carried by the target
    -- localization in both the local map and its maximal ideal.
    letI : CommRing (Localization.AtPrime n) := OreLocalization.instCommRing
    (Localization.localRingHom m n (algebraMap A₁ B₁) (n.over_def m)).formally_smooth_for_adic
      (maximalIdeal (Localization.AtPrime n)) := sorry
-- Proof strategy: base-change `hfs` along `A → A₁` with
-- `RingHom.formally_smooth_for_adic_baseChange`, then compare `A₁ ⊗[A] B` with the integral
-- closure `B₁` through `integralClosure.BaseChange.tensorMap`.  Formal smoothness makes the
-- nilpotent reduction and normalization comparison an equivalence on the selected branch.  Localize
-- this comparison at `m` and `n`, transport the mapped adic ideal through the resulting local-ring
-- equivalence, and identify it with `maximalIdeal (Localization.AtPrime n)` using `n.LiesOver m`.

end

end DVR.Field.BaseChange
