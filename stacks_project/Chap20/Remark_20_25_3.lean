/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Shift.CommShift
public import stacks_project.Chap20.Lemma_20_25_1

/-! @stack 0FLI -/

@[expose] public section

open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u}
/- Domain-style sampling for Remark `20.25.3`.
- primary domain: shift compatibility of the bounded-below Čech-to-derived-global-sections
  comparison morphism from Lemma `20.25.1`;
- sampled owner declarations:
  `moduleCechDerivedFunctor`,
  `exists_moduleCechToDerivedGlobalSections`,
  `NatTrans.CommShift`,
  `NatTrans.shift_app_comm`;
- best owner abstraction:
  `source-facing`: the Chapter 20 comparison morphism chosen from
    `exists_moduleCechToDerivedGlobalSections X 𝒰 h𝒰`;
  `core/canonical`: `NatTrans.CommShift τ ℤ`, `NatTrans.shift_app_comm τ`, and `CommSq`;
  `bridge/view`: the shifted identity `NatTrans.shift_app_comm τ n K` and its square form
    `CommSq.mk (NatTrans.shift_app_comm τ n K)`, used directly instead of introducing a second
    Chapter 20 comparison API.
- primitive data vs. derived API: the only source-facing primitive datum is the comparison
  natural transformation `τ`; its shift-compatibility and shifted square are derived canonically
  from `NatTrans.CommShift`, `NatTrans.shift_app_comm`, and `CommSq.mk`.

Source/core/bridge triage:
- `source-facing`: the existence theorem below, matching the textbook remark that the comparison
  map may be chosen compatibly with shifts;
- `core/canonical`: the owner predicate `NatTrans.CommShift τ ℤ` and its canonical evaluation
  formula `NatTrans.shift_app_comm τ`;
- `bridge/view`: the corresponding shifted commutative square obtained by `CommSq.mk`.

This file therefore keeps only the source-facing existence theorem and reuses the canonical shift
owner directly, rather than introducing a second Chapter 20 theorem for the shifted square. -/

section

variable (𝒰 : ι → Opens X.carrier)

local notation "CechF" => moduleCechDerivedFunctor X 𝒰
local notation "KplusToDplusModX" =>
  (DerivedCategory.Plus.Q : CochainComplex.Plus X.Modules ⥤
    DerivedCategory.Plus X.Modules)
local notation "RΓplus" => Module.Derived.GlobalSections.Bounded.functor X

/-- Remark 20.25.3: once the source and target functors are equipped with their shift-commuting
structures, one may choose the comparison morphism of Lemma `20.25.1` so that the resulting
source-facing comparison itself satisfies the canonical shift-compatibility owner
`NatTrans.CommShift`. -/
@[stacks 0FLI]
theorem exists_moduleCechToDerivedGlobalSections_commShift
    (h𝒰 : iSup 𝒰 = ⊤)
    [(CechF).CommShift ℤ] [((KplusToDplusModX ⋙ RΓplus)).CommShift ℤ] :
    ∃ τ : CechF ⟶ KplusToDplusModX ⋙ RΓplus,
      IsModuleCechToDerivedGlobalSectionsComparison X 𝒰 τ ∧
        NatTrans.CommShift τ ℤ := sorry

/- For any chosen comparison `τ` with a witness `hτshift : NatTrans.CommShift τ ℤ`,
installing `letI := hτshift` recovers the canonical owner formula
`NatTrans.shift_app_comm τ n K`; applying `CommSq.mk` to that equality yields the corresponding
commutative square. No parallel Chapter 20 wrapper theorem is kept here, because that square is
already the direct bridge/view supplied by the owner formula. -/

end

end AlgebraicGeometry.RingedSpace
