module

public import ReasLib.Algebra.Category.ModuleCat.ExteriorPower.Sequence
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Epi
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.LeftTensor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Exterior-power sequences on ringed sites

This file packages the two canonical exterior-power morphisms associated to a short complex as
a reusable short complex. Exactness is stated for exact pairs with epimorphic final map, matching
the right-exact input used by the algebraic exterior-power theorem.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.ExteriorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

/-- The two morphisms in the exterior-power sequence associated to `S` compose to zero. -/
theorem sequenceCompEqZero
    (S : ShortComplex (ringedSiteModuleCategory J 𝒪)) (n : ℕ) :
    leftTensorMap 𝒪 S.f n ≫ map 𝒪 S.g (n + 1) = 0 := sorry

/-- The exterior-power short complex associated to `S` in degree `n + 1`:
`S.X₁ ⊗ Λ^n(S.X₂) ⟶ Λ^(n + 1)(S.X₂) ⟶ Λ^(n + 1)(S.X₃)`. -/
@[stacks 01CJ "exterior-power sequence on a ringed site"]
noncomputable def sequence
    (S : ShortComplex (ringedSiteModuleCategory J 𝒪)) (n : ℕ) :
    ShortComplex (ringedSiteModuleCategory J 𝒪) :=
  ShortComplex.mk (leftTensorMap 𝒪 S.f n) (map 𝒪 S.g (n + 1))
    (sequenceCompEqZero 𝒪 S n)

/-- The first morphism of the exterior-power sequence is the canonical left-tensor map. -/
@[simp]
theorem sequence_f
    (S : ShortComplex (ringedSiteModuleCategory J 𝒪)) (n : ℕ) :
    (sequence 𝒪 S n).f = leftTensorMap 𝒪 S.f n := sorry

/-- The second morphism of the exterior-power sequence is the induced exterior-power map. -/
@[simp]
theorem sequence_g
    (S : ShortComplex (ringedSiteModuleCategory J 𝒪)) (n : ℕ) :
    (sequence 𝒪 S n).g = map 𝒪 S.g (n + 1) := sorry

/-- An exact pair of module sheaves whose final map is epimorphic induces an exact
exterior-power pair. -/
theorem sequence_exact
    (S : ShortComplex (ringedSiteModuleCategory J 𝒪)) (n : ℕ)
    (hS : S.Exact) [Epi S.g] :
    (sequence 𝒪 S n).Exact := sorry

/-- The final map of the exterior-power sequence is epimorphic whenever the final map of `S`
is. -/
instance sequence_epi
    (S : ShortComplex (ringedSiteModuleCategory J 𝒪)) (n : ℕ) [Epi S.g] :
    Epi (sequence 𝒪 S n).g := sorry

/-- Lemma 17.21.4 (01CJ), exterior case: an exact pair of module sheaves whose final map is
epimorphic induces a right-exact exterior-power pair. -/
@[stacks 01CJ "right-exact exterior-power sequence on a ringed site"]
theorem sequence_exact_and_epi
    (S : ShortComplex (ringedSiteModuleCategory J 𝒪)) (n : ℕ)
    (hS : S.Exact) [Epi S.g] :
    (sequence 𝒪 S n).Exact ∧ Epi (sequence 𝒪 S n).g := sorry

end SheafOfModules.RingedSite.ExteriorPower
