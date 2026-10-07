module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Length.Local
public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Length.Projective
import StacksCheckRecall

/-!
# Example 10.55.2

@stack 00JE
-/

@[expose] public section

open CategoryTheory

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable (k : Type u) [Field k]

/- Domain-style sampling for Example 10.55.2:
- primary domain: the comparison between `K₀(k)` of finite projective `k`-modules and `K'_0(k)`
  of finite `k`-modules, identified with `ℤ` by rank/length;
- sampled owner declarations:
  `ModuleCat.K0.finiteLength_comp_projectiveToFinite`,
  `ModuleCat.K0.finiteLength_projectiveToFinite`,
  `ModuleCat.K0.finiteLengthEquiv`,
  `ModuleCat.K0.finiteLengthEquiv_apply`,
  `ModuleCat.K0.finiteLengthEquiv_symm_apply`,
  `ModuleCat.K0.Finite.ofLength`,
  `ModuleCat.K0.Projective.rank`;
- best owner abstraction:
  the canonical owner data is the comparison square from Lemma 10.55.9 together with the explicit
  residue-field inverse behind `ModuleCat.K0.finiteLengthEquiv`; this file is a field-specific
  `bridge/view`, not a new owner;
- primitive vs. derived:
  primitive data remains the comparison map `K₀(k) → K'_0(k)` and the rank/length homomorphisms;
  the field statement is the derived specialization where `length_k(k) = 1`;
- source/core/bridge triage:
  `source-facing`: Example 10.55.2 identifying the canonical comparison with the dimension map;
  `core/canonical`: `ModuleCat.K0.finiteLength_comp_projectiveToFinite` and
  `ModuleCat.K0.finiteLengthEquiv`;
  `bridge/view`: the field specialization below.
-/
/-- Over a field `k`, the canonical comparison map `K₀(k) → K'_0(k)` commutes with the rank and
length identifications with `ℤ`. -/
@[stacks 00JE "rank and length comparison square"]
theorem field_projectiveGrothendieckGroup_comparison_commutes_with_rank :
    (ModuleCat.K0.finiteLengthEquiv k).toAddMonoidHom.comp
        (ModuleCat.K0.projectiveToFinite k) =
      ModuleCat.K0.Projective.rank k := sorry

/-- Example 10.55.2: if `R = k` is a field, then the canonical map `K₀(k) → K'_0(k)` is the
identification obtained by the dimension function, which over a field is also the length function.
Equivalently, the comparison map is the canonical passage through `ℤ`. -/
@[stacks 00JE]
theorem field_projectiveGrothendieckGroup_to_finiteGrothendieckGroup_eq :
    ModuleCat.K0.projectiveToFinite k =
      (ModuleCat.K0.finiteLengthEquiv k).symm.toAddMonoidHom.comp
        (ModuleCat.K0.Projective.rank k) := sorry
