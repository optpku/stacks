/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import ReasLib.CategoryTheory.Sites.Cohomology.LocallyZero
public import ReasLib.CategoryTheory.Sites.Cohomology.Presheaf
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Sheaf

import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# A situation for comparing cohomology on two topologies

This leaf owns the reusable comparison data used by the cohomology-comparison lemmas. The
canonical API is organized under the short `TopologyComparison.Situation` namespace.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe u v i j k

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]

namespace TopologyComparison

/-- Closure and refinement conditions for comparing cohomology of two topologies.
The family `A'` specifies coefficient sheaves on each slice, and `P` specifies the morphisms
along which higher direct images and covering refinements are controlled. -/
@[stacks 0EZ3]
class Situation
    (τ τ' : GrothendieckTopology C)
    (P : MorphismProperty C)
    (A' : ∀ X : C,
      ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v})) : Prop where
  /-- Each `A'_X` is a weak Serre subcategory. -/
  isWeakSerre (X : C) : IsWeakSerreClass (A' X)
  /-- Pullbacks of arrows in `P` exist. -/
  hasPullbacks : P.HasPullbacks
  /-- The morphism property `P` is stable under base change. -/
  isStableUnderBaseChange : P.IsStableUnderBaseChange
  /-- Inverse image along a morphism preserves the chosen coefficient families. -/
  inverseImage_mem {X Y : C} (f : X ⟶ Y)
      {ℱ : Sheaf (τ'.over Y) AddCommGrpCat.{max u v}} (_ : A' Y ℱ) :
      A' X ((τ'.overMapPullback AddCommGrpCat.{max u v} f).obj ℱ)
  /-- Every chosen `τ'`-coefficient sheaf also satisfies the finer `τ`-sheaf condition. -/
  isSheaf_for_finer_topology {X : C}
      {ℱ : Sheaf (τ'.over X) AddCommGrpCat.{max u v}} (_ : A' X ℱ) :
      Presheaf.IsSheaf (τ.over X) ℱ.1
  /-- Higher direct images along arrows in `P` remain in the chosen families. -/
  higherDirectImage_mem
      [∀ X : C, HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
      [∀ X : C, HasInjectiveResolutions
        (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
      [∀ {X Y : C} (f : X ⟶ Y),
        Functor.Additive
          ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
            (τ'.over X) (τ'.over Y))]
      {X Y : C} (f : X ⟶ Y) (_ : P f) (i : ℕ)
      {ℱ : Sheaf (τ'.over X) AddCommGrpCat.{max u v}} (_ : A' X ℱ) :
      A' Y ((((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
        (τ'.over X) (τ'.over Y)).rightDerived i).obj ℱ)
  /-- Every finer covering family admits a coarser cover followed by singleton finer covers
  in `P` and coarser covers factoring through the original family. -/
  tau_covering_refinement {U : C} {ι : Type i} (cover : ι → Over U)
      (_ : (τ.over U).CoversTop cover) :
      ∃ (J : Type j) (V : J → Over U),
        (τ'.over U).CoversTop V ∧
          ∃ (W : J → C) (f : ∀ j, W j ⟶ (V j).left),
            ∀ j,
              P (f j) ∧
                Sieve.generate (Presieve.singleton (f j)) ∈ τ (V j).left ∧
                  ∃ (Kj : Type k) (Wcoverj : Kj → Over (W j)),
                    (τ'.over (W j)).CoversTop Wcoverj ∧
                      ∀ k : Kj,
                        ∃ i : ι,
                          Nonempty
                            ((Over.mk ((Wcoverj k).hom ≫ f j ≫ (V j).hom)) ⟶ cover i)

attribute [instance] Situation.isWeakSerre Situation.hasPullbacks
  Situation.isStableUnderBaseChange

namespace Situation

variable {τ τ' : GrothendieckTopology C}
variable {P : MorphismProperty C}
variable {A' : ∀ X : C,
  ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v})}

/-- A chosen coefficient sheaf, equipped with its finer `τ`-sheaf structure. -/
@[stacks 0EZ3 "finer-topology coefficient sheaf"]
def finerSheaf
    (h : Situation τ τ' P A')
    {X : C} {ℱ : Sheaf (τ'.over X) AddCommGrpCat.{max u v}} (hℱ : A' X ℱ) :
    Sheaf (τ.over X) AddCommGrpCat.{max u v} :=
  ⟨ℱ.1, h.isSheaf_for_finer_topology hℱ⟩

/-- The underlying presheaf of `finerSheaf` is the original coefficient presheaf. -/
@[simp]
theorem coe_finerSheaf
    (h : Situation τ τ' P A')
    {X : C} {ℱ : Sheaf (τ'.over X) AddCommGrpCat.{max u v}} (hℱ : A' X ℱ) :
    (h.finerSheaf hℱ).1 = ℱ.1 := sorry

/-- A coefficient sheaf already satisfying the finer topology's sheaf condition agrees with its
canonical topology-comparison inverse image.  This concrete `Iso` is the reusable root; the
`IsIsomorphic` theorem below is only its proposition-level compatibility view. -/
@[stacks 0EZ3 "selected finer sheaf as topology-comparison inverse image"]
noncomputable def finerSheafIsoPullback
    (h : Situation τ τ' P A') (hle : τ' ≤ τ) {X : C}
    [HasWeakSheafify (τ.over X) AddCommGrpCat.{max u v}]
    {ℱ : Sheaf (τ'.over X) AddCommGrpCat.{max u v}} (hℱ : A' X ℱ) :
    h.finerSheaf hℱ ≅ (comparisonTopologyPullbackAb hle X).obj ℱ :=
  (comparisonTopologyPullbackIsoOfIsSheaf
    AddCommGrpCat.{max u v} hle X ℱ (h.isSheaf_for_finer_topology hℱ)).symm

/-- Proposition-level view of `finerSheafIsoPullback`. -/
@[stacks 0EZ3 "finer-topology sheaf as topology-comparison inverse image"]
theorem finerSheaf_isomorphic_pullback
    (h : Situation τ τ' P A') (hle : τ' ≤ τ) {X : C}
    [HasWeakSheafify (τ.over X) AddCommGrpCat.{max u v}]
    {ℱ : Sheaf (τ'.over X) AddCommGrpCat.{max u v}} (hℱ : A' X ℱ) :
    IsIsomorphic (h.finerSheaf hℱ)
      ((comparisonTopologyPullbackAb hle X).obj ℱ) := sorry

/-- The comparison-adjunction unit is invertible on coefficients selected by a comparison
situation. -/
@[stacks 0EZ3 "comparison unit on selected coefficients"]
theorem unit_isIso
    (h : Situation τ τ' P A') (hle : τ' ≤ τ) {X : C}
    [HasWeakSheafify (τ.over X) AddCommGrpCat.{max u v}]
    {ℱ : Sheaf (τ'.over X) AddCommGrpCat.{max u v}} (hℱ : A' X ℱ) :
    IsIso ((comparisonTopologyAdjunction AddCommGrpCat.{max u v} hle X).unit.app ℱ) := sorry

variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{max u v})]

/-- The cohomology presheaf used to formulate the local comparison condition. -/
@[stacks 0EZ3 "selected cohomology presheaf"]
noncomputable def selectedCohomologyPresheaf
    (h : Situation τ τ' P A') {X : C}
    (ℱ : Sheaf (τ'.over X) AddCommGrpCat.{max u v}) (hℱ : A' X ℱ) (n : ℕ) :
    (Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  Sheaf.uliftCohomologyPresheaf (τ.over X) (h.finerSheaf hℱ) (n + 1)

/-- Every section of the degree `n + 1` cohomology presheaf of a chosen coefficient sheaf
vanishes locally for the coarser topology. -/
@[stacks 0EZ3]
def LocalVanishing
    (h : Situation τ τ' P A') (n : ℕ) : Prop :=
  ∀ (X : C) (ℱ : Sheaf (τ'.over X) AddCommGrpCat.{max u v}) (hℱ : A' X ℱ)
    (U : Over X) (ξ : (h.selectedCohomologyPresheaf ℱ hℱ n).obj (Opposite.op U)),
      Presheaf.IsLocallyZero (τ'.over X)
        (h.selectedCohomologyPresheaf ℱ hℱ n) ξ

/- A reusable certificate for the all-degree conclusion proved from a comparison situation. -/
/-- The all-degree local vanishing predicate `∀ n, (V_n)`. -/
@[stacks 0EZF "all-degree local vanishing predicate"]
def AllVanishing (h : Situation τ τ' P A') : Prop :=
  ∀ n : ℕ, LocalVanishing h n

end Situation

variable {τ τ' : GrothendieckTopology C}

/-- The coefficient object property obtained by pulling `A'_X` back along `ε_{X,*}`. -/
@[stacks 0EZ9]
def objectProperty
    (hle : τ' ≤ τ)
    (A' : ∀ X : C,
      ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    (X : C) :
    ObjectProperty (Sheaf (τ.over X) AddCommGrpCat.{max u v}) :=
  (A' X).inverseImage (comparisonTopologyPushforwardAb hle X)

/-- Membership in `TopologyComparison.objectProperty` is membership after `ε_{X,*}`. -/
@[stacks 0EZ9]
theorem objectProperty_mem_iff
    (hle : τ' ≤ τ)
    (A' : ∀ X : C,
      ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    {X : C} {ℱ : Sheaf (τ.over X) AddCommGrpCat.{max u v}} :
    objectProperty hle A' X ℱ ↔
      A' X ((comparisonTopologyPushforwardAb hle X).obj ℱ) := sorry

/-- Pullback along a morphism of the site preserves the coefficient property induced from a
topology-comparison situation. -/
@[stacks 0EZ9 "comparison coefficient property is stable under pullback"]
theorem objectProperty_le_pullback
    {τ τ' : GrothendieckTopology C} {P : MorphismProperty C}
    {A' : ∀ X : C,
      ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v})}
    (h : Situation τ τ' P A') (hle : τ' ≤ τ)
    {X Y : C} (f : X ⟶ Y) :
    objectProperty hle A' Y ≤
      (objectProperty hle A' X).inverseImage
        (τ.overMapPullback AddCommGrpCat.{max u v} f) := sorry

/- Source-facing notation for `A_X = ε_{X,*}^{-1}(A'_X)`. -/
scoped notation "A[" hle ", " A' "]_(" X ")" => objectProperty hle A' X

end TopologyComparison

scoped notation "(V_" n ")" => fun h ↦ TopologyComparison.Situation.LocalVanishing h n

/- The specialization only instantiates the explicit generic comparison `Iso`; any `sorryAx`
below is inherited from its Prop-valued topology and sheafification laws. -/

end CategoryTheory.GrothendieckTopology

end
