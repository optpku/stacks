/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.BaseChange.FormalSmooth
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Tame
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Abhyankar's lemma for DVR base change

This leaf owns the formal-smoothness conclusion of the current Stacks Lemma 15.116.4.  Tameness
is expressed through separability of the residue-field extension and the canonical
`DVR.Field.PrimeToResidueChar` predicate; the base-change normalization is the existing reduced
tensor-product owner.

@stack 0BRM
-/

open IsLocalRing
open IsExtensionOfDiscreteValuationRings
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

/-- Lemma 15.115.4 (Abhyankar's lemma) (0BRM): let `A ⊂ B` be a tame extension of discrete
valuation rings and let `K1 / K` be finite.  If the ramification index of `A ⊂ B` divides the
ramification index at a maximal branch `m` of `A₁`, then every branch above `m` is formally smooth
for its maximal-ideal-adic topology. -/
@[stacks 0BRM "Abhyankar formal smoothness after tame base change"]
theorem formallySmoothAtOfTameAndDvd
    (hsep : Algebra.IsSeparable (ResidueField A) (ResidueField B))
    (hprime : PrimeToResidueChar A (ramificationIndex A B))
    (m : Ideal A₁) [m.IsMaximal]
    (n : Ideal B₁) [n.IsMaximal] [n.LiesOver m]
    (hdvd : ramificationIndex A B ∣ m.ramificationIdx A) :
    -- Local instance justification (defeq pin): use the `CommRing` model carried by the target
    -- localization in both the local map and its maximal ideal.
    letI : CommRing (Localization.AtPrime n) := OreLocalization.instCommRing
    (Localization.localRingHom m n (algebraMap A₁ B₁) (n.over_def m)).formally_smooth_for_adic
      (maximalIdeal (Localization.AtPrime n)) := sorry
-- Proof strategy: write `e = ramificationIndex A B` and use `hdvd` to insert the standard
-- uniformizer-root extension of degree `e` inside the branch at `m`.  The prime-to-residue-
-- characteristic hypothesis makes this Kummer layer tame, while `hsep` supplies the residue-field
-- separability.  Apply `DVR.Field.BaseChange.formallySmoothAt` to the resulting base-change square;
-- multiplicativity of ramification indices makes the remaining upper branch weakly unramified.
-- Transport weak unramifiedness and residue separability back across the finite étale unit-root
-- layer, then conclude with
-- `formally_smooth_for_maximalIdeal_adic_iff_weakly_unramified_and_separable_residueField`.

end

end DVR.Field.BaseChange
