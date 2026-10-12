/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.Polynomial
import StacksCheckRecall

@[expose] public section

/-!
# Indexed divided-power polynomial algebras

The finite-subset transition maps and the indexed divided-power polynomial universal property
are reusable `DPPolynomial` API.  This file is the source-label facade for Remark 23.5.2.
-/

open DividedPowers

noncomputable section

universe uA uW uC

section Source

variable (A : Type uA) [CommRing A] (W : Type uW)
variable (E F : Finset W) (h : E ⊆ F)

/- Remark 23.5.2 (1) (07H6): an inclusion of finite sets of variables induces the uniquely
characterized transition map between the corresponding divided-power polynomial algebras. -/
@[stacks 07H6 "(1)"]
#check (DPPolynomial.FiniteSubset.existsUnique_map A h :
  ∃! φ : DPPolynomial.FiniteSubset.Ring A E →ₐ[A]
      DPPolynomial.FiniteSubset.Ring A F,
    ∀ (n : ℕ) (m : E →₀ A),
      φ (DividedPowerAlgebra.dp A n m) =
        DividedPowerAlgebra.dp A n
          (DPPolynomial.FiniteSubset.linearMap A h m))

variable {B : Type uC} [CommRing B] [Algebra A B]
variable (φ : ∀ E : Finset W, DPPolynomial.FiniteSubset.Ring A E →ₐ[A] B)
variable (hφ : DPPolynomial.FiniteSubset.IsCompatible A φ)

/- Remark 23.5.2 (2) (07H6): the indexed divided-power polynomial algebra has the universal
property of the colimit of the algebras on finite subsets of variables. -/
@[stacks 07H6 "(2)"]
#check (DPPolynomial.FiniteSubset.existsUnique_desc A φ hφ :
  ∃! g : DPPolynomial A W →ₐ[A] B,
    DPPolynomial.FiniteSubset.IsDesc A φ g)

variable (I : Ideal A) (γ : DividedPowers I)

/- Remark 23.5.2 (3) (07H6): the indexed divided-power polynomial ideal has a unique compatible
divided-power structure extending the one on the base ideal. -/
@[stacks 07H6 "(3)"]
#check (DPPolynomial.existsUnique_dividedPowers (ι := W) γ :
  ∃! delta : DividedPowers (DPPolynomial.ideal A W I),
    DPPolynomial.IsCanonical γ delta)

variable {C : Type uC} [CommRing C] (K : Ideal C) (ε : DividedPowers K)
variable (f : DPMorphism γ ε) (x : W → K)

/- Remark 23.5.2 (4) (07H6): maps from an indexed divided-power polynomial algebra are uniquely
determined by a divided-power base map and target-ideal values for the variables. -/
@[stacks 07H6 "(4)"]
#check (DPPolynomial.existsUnique_lift f x :
  ∃! phi : DPPolynomial A W →+* C,
    DPPolynomial.IsLift (DPPolynomial.dividedPowers γ) f x phi)

end Source

#check @DPPolynomial.FiniteSubset.existsUnique_map
#check @DPPolynomial.FiniteSubset.existsUnique_desc
#check @DPPolynomial.existsUnique_dividedPowers
#check @DPPolynomial.dividedPowers
#check @DPPolynomial.dividedPowers_isCanonical
#check @DPPolynomial.dividedPowers_dpow_X
#check @DPPolynomial.dividedPowers_dpow_algebraMap
#check @DPPolynomial.dividedPowers_dpow_dp
#check @DPPolynomial.isCanonical_iff_eq_dividedPowers
#check @DPPolynomial.exists_isCanonical
#check @DPPolynomial.IsCanonical.eq
#check @DPPolynomial.IsCanonical.eq_dividedPowers
#check @DPPolynomial.existsUnique_lift
#check @DPPolynomial.FiniteSubset.inclusion
#check @DPPolynomial.FiniteSubset.linearMap
#check @DPPolynomial.FiniteSubset.map
#check @DPPolynomial.FiniteSubset.toIndexed
#check @DPPolynomial.FiniteSubset.IsCompatible
#check @DPPolynomial.FiniteSubset.toIndexed_dp_support
#check @DPPolynomial.FiniteSubset.descValue
#check @DPPolynomial.FiniteSubset.descValue_eq_of_support_subset
#check @DPPolynomial.FiniteSubset.desc
#check @DPPolynomial.FiniteSubset.IsDesc
#check @DPPolynomial.FiniteSubset.desc_apply_dp
#check @DPPolynomial.FiniteSubset.desc_comp_toIndexed
#check @DPPolynomial.FiniteSubset.desc_unique
#check @DPPolynomial.FiniteSubset.diagram
#check @DPPolynomial.FiniteSubset.cocone
#check @DPPolynomial.FiniteSubset.coconeMap
#check @DPPolynomial.FiniteSubset.coconeMap_isCompatible
#check @DPPolynomial.FiniteSubset.colimitDesc
#check @DPPolynomial.FiniteSubset.isColimit
#check @DPPolynomial.rename
#check @DPPolynomial.rename_apply_dp
#check @DPPolynomial.renameDP
#check @DPPolynomial.renameDP_X
#check @DPPolynomial.renameDP_comp
#check @DPPolynomial.map
#check @DPPolynomial.map_apply_dp
#check @DPPolynomial.map_X
#check @DPPolynomial.map_comp
#check @DPPolynomial.renameDP_naturality
#check @DPPolynomial.lift
#check @DPPolynomial.lift_apply_dp
#check @DPPolynomial.dpLift
#check @DPPolynomial.dpLift_apply_dp
#check @DPPolynomial.existsUnique_dpLift
