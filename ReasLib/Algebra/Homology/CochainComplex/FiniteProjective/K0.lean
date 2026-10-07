module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Basic
public import ReasLib.Algebra.Homology.CochainComplex.FiniteProjective.Triangulated
public import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Tactic.CrossRefAttribute

/-!
# Euler classes of finite-projective complexes

The alternating `K₀` class of a bounded finite-projective cochain complex is a concrete complex
level datum.  Representative-independence and additivity are exposed as separate Prop lemmas for
the derived-category owners.

@stack 0AFY
-/

@[expose] public section

open CategoryTheory
open scoped BigOperators

noncomputable section

universe u

namespace CochainComplex

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

/-- The alternating-sum Euler class of a bounded finite-projective complex in `K₀(R)`. -/
@[stacks 0AFY "Euler class of a bounded finite-projective complex"]
noncomputable def eulerCharacteristic
    (L : Cpx) [hL : IsBoundedFiniteProjective L] : ModuleCat.K0.projective R :=
  ∑ᶠ i : ℤ,
    i.negOnePow •
      ModuleCat.K0.projectiveOf R
        ⟨L.X i, ⟨hL.finite i, hL.projective i⟩⟩

/-- A bounded support interval computes the Euler class by an ordinary finite sum. -/
@[stacks 0AFY "finite support formula for the Euler class"]
theorem eulerCharacteristic_eq_sum_Icc
    (L : Cpx) [IsBoundedFiniteProjective L] {a b : ℤ}
    (hge : L.IsStrictlyGE a) (hle : L.IsStrictlyLE b) :
    L.eulerCharacteristic =
      Finset.sum (Finset.Icc a b) fun i ↦
        i.negOnePow •
          ModuleCat.K0.projectiveOf R
            ⟨L.X i, ⟨inferInstance, inferInstance⟩⟩ := sorry
-- Proof strategy: unfold `eulerCharacteristic`; use `hge` and `hle` to show its summand vanishes
-- outside `Finset.Icc a b`, then apply the finite-support computation rule for `finsum`.

/-- Shifting a bounded finite-projective complex multiplies its Euler class by `(-1)^n`. -/
@[stacks 0AFY "shift formula for the Euler class"]
theorem eulerCharacteristic_shift
    (L : Cpx) [IsBoundedFiniteProjective L] (n : ℤ) :
    (L⟦n⟧).eulerCharacteristic = n.negOnePow • L.eulerCharacteristic := sorry
-- Proof strategy: choose a common finite support interval, expand both Euler classes with
-- `eulerCharacteristic_eq_sum_Icc`, reindex by the shift translation on `ℤ`, and simplify the
-- signs using multiplicativity of `Int.negOnePow`.

/-- An acyclic bounded finite-projective complex has zero Euler class. -/
@[stacks 0AFY "acyclic Euler class vanishing"]
theorem eulerCharacteristic_eq_zero_of_acyclic
    (L : Cpx) [IsBoundedFiniteProjective L] (hAcyclic : L.Acyclic) :
    L.eulerCharacteristic = 0 := sorry
-- Proof strategy: expand over a bounded interval and telescope the alternating sum using the
-- short exact rows of boundaries, cycles, and terms supplied by acyclicity; each row contributes
-- the defining projective `K₀` relation.

/-- The mapping-cone Euler class satisfies the distinguished-triangle relation. -/
@[stacks 0AFY "mapping-cone Euler class additivity"]
theorem eulerCharacteristic_add_of_mappingCone
    {L M : Cpx} (f : L ⟶ M)
    [IsBoundedFiniteProjective L] [IsBoundedFiniteProjective M] :
    M.eulerCharacteristic =
      L.eulerCharacteristic + (CochainComplex.mappingCone f).eulerCharacteristic := sorry
-- Proof strategy: choose finite support bounds for `L` and `M`, expand all three Euler classes,
-- identify each cone term with the product of `M.X i` and the shifted `L.X`, use the projective
-- `K₀` product relation, and reindex the shifted summands.

/-- Quasi-isomorphic bounded finite-projective complexes have equal Euler classes. -/
@[stacks 0AFY "quasi-isomorphic Euler classes"]
theorem eulerCharacteristic_eq_of_quasiIso
    {L M : Cpx} (f : L ⟶ M)
    [IsBoundedFiniteProjective L] [IsBoundedFiniteProjective M] [QuasiIso f] :
    L.eulerCharacteristic = M.eulerCharacteristic := sorry
-- Proof strategy: the mapping cone of a quasi-isomorphism is acyclic; combine
-- `eulerCharacteristic_add_of_mappingCone` with
-- `eulerCharacteristic_eq_zero_of_acyclic` and cancel the zero cone term.

end CochainComplex

end
