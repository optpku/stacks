/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Prod
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Topology.Algebra.Group.GroupTopology
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Instances.Rat

/-!
# A sequential system of abelian topological groups with distinct colimit topologies

The stages are `ℚ × ℝ^{n+1}` with the Euclidean product topology, and the
successor maps pad a trailing zero on the real coordinates. The algebraic sequential
colimit is `ℚ × (ℕ →₀ ℝ)`. Its colimit topology in `TopCat` is the final topology of
the stage inclusions; its colimit topology in topological groups is the finest additive
group topology making those inclusions continuous.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped Topology

namespace TopCat.Counterexample.NatAddGroupColimit

/-- The `n`-th stage is the product of the rationals and `n + 1` real coordinates. -/
abbrev stage (n : ℕ) : Type :=
  ℚ × (Fin (n + 1) → ℝ)

/-- The rational-real product stage bundled with its Euclidean product topology. -/
def stageSpace (n : ℕ) : TopCat.{0} :=
  TopCat.of (stage n)

/-- The algebraic sequential colimit of the stages. -/
abbrev colimitCarrier : Type :=
  ℚ × (ℕ →₀ ℝ)

noncomputable section

/-- The additive successor `(q, v) ↦ (q, Fin.snoc v 0)`, via zero-padding along
`Fin.castSuccEmb`. -/
def stageTransitionHom (n : ℕ) : stage n →+ stage (n + 1) :=
  (AddMonoidHom.id ℚ).prodMap <|
    (Finsupp.addEquivFunOnFinite :
        (Fin (n + 2) →₀ ℝ) ≃+ (Fin (n + 2) → ℝ)).toAddMonoidHom.comp
      ((Finsupp.embDomain.addMonoidHom (Fin.castSuccEmb : Fin (n + 1) ↪ Fin (n + 2))).comp
        (Finsupp.addEquivFunOnFinite :
            (Fin (n + 1) →₀ ℝ) ≃+ (Fin (n + 1) → ℝ)).symm.toAddMonoidHom)

/-- The additive successor pads a trailing zero on the real coordinates. -/
theorem stageTransitionHom_apply (n : ℕ) (q : ℚ) (v : Fin (n + 1) → ℝ) :
    stageTransitionHom n (q, v) = (q, Fin.snoc v 0) :=
  sorry

/-- The Euclidean successor maps are continuous. -/
theorem stageTransition_continuous (n : ℕ) :
    Continuous (stageTransitionHom n : stage n → stage (n + 1)) :=
  sorry

/-- The continuous successor morphism between adjacent bundled stage spaces. -/
def stageTransition (n : ℕ) : stageSpace n ⟶ stageSpace (n + 1) :=
  TopCat.ofHom ⟨stageTransitionHom n, stageTransition_continuous n⟩

/-- The successor maps are closed embeddings. -/
theorem isClosedEmbedding_stageTransition (n : ℕ) :
    Topology.IsClosedEmbedding (stageTransitionHom n : stage n → stage (n + 1)) :=
  sorry

/-- The rational-real product stages and zero-padding maps form a sequential diagram. -/
def system : ℕ ⥤ TopCat.{0} :=
  Functor.ofSequence stageTransition

/-- The objects of `system` are the bundled stage spaces. -/
theorem system_obj (n : ℕ) : system.obj n = stageSpace n :=
  sorry

/-- The algebraic inclusion of stage `n` into the finite-support colimit carrier. -/
def stageι (n : ℕ) : stage n →+ colimitCarrier :=
  (AddMonoidHom.id ℚ).prodMap <|
    (Finsupp.embDomain.addMonoidHom Fin.valEmbedding).comp
      (Finsupp.addEquivFunOnFinite :
          (Fin (n + 1) →₀ ℝ) ≃+ (Fin (n + 1) → ℝ)).symm.toAddMonoidHom

/-- The stage inclusion extends the real coordinates by zero to a finitely supported function. -/
theorem stageι_apply (n : ℕ) (q : ℚ) (v : Fin (n + 1) → ℝ) :
    stageι n (q, v) =
      (q, Finsupp.embDomain Fin.valEmbedding (Finsupp.equivFunOnFinite.symm v)) :=
  sorry

/-- Each algebraic stage inclusion is injective. -/
theorem stageι_injective (n : ℕ) :
    Function.Injective (stageι n : stage n → colimitCarrier) :=
  sorry

/-- The algebraic stage inclusions commute with zero-padding successor maps. -/
theorem stageι_comp_stageTransitionHom (n : ℕ) :
    (stageι (n + 1)).comp (stageTransitionHom n) = stageι n :=
  sorry

/-- The colimit topology of `system` in topological spaces: the final topology of the
stage inclusions. -/
@[implicit_reducible]
def spaceColimitTopology : TopologicalSpace colimitCarrier :=
  ⨆ n, coinduced (stageι n : stage n → colimitCarrier) inferInstance

/-- The colimit topology of `system` in topological groups: the finest additive group
topology making every stage inclusion continuous. -/
def groupColimitTopology : AddGroupTopology colimitCarrier :=
  sInf { t : AddGroupTopology colimitCarrier |
    ∀ n, Continuous[inferInstance, t.toTopologicalSpace] (stageι n) }

/-- A set is open in the space-colimit topology if and only if every stage preimage is
open. -/
theorem isOpen_spaceColimitTopology_iff (U : Set colimitCarrier) :
    IsOpen[spaceColimitTopology] U ↔
      ∀ n, IsOpen ((stageι n : stage n → colimitCarrier) ⁻¹' U) :=
  sorry

/-- Each stage inclusion is continuous for the space-colimit topology. -/
theorem continuous_stageι_spaceColimitTopology (n : ℕ) :
    Continuous[inferInstance, spaceColimitTopology] (stageι n) :=
  sorry

/-- Each stage inclusion is continuous for the group-colimit topology. -/
theorem continuous_stageι_groupColimitTopology (n : ℕ) :
    Continuous[inferInstance, groupColimitTopology.toTopologicalSpace] (stageι n) :=
  sorry

/-- `colimitCarrier` bundled with the topological-space colimit topology. -/
def spaceColimit : TopCat.{0} :=
  @TopCat.of colimitCarrier spaceColimitTopology

/-- The topological inclusion of stage `n` into the space-colimit. -/
def spaceι (n : ℕ) : stageSpace n ⟶ spaceColimit :=
  @TopCat.ofHom (stage n) colimitCarrier inferInstance spaceColimitTopology <|
    @ContinuousMap.mk (stage n) colimitCarrier inferInstance spaceColimitTopology
      (stageι n) (continuous_stageι_spaceColimitTopology n)

/-- The topological cocone legs commute with successor maps. -/
theorem spaceι_naturality (n : ℕ) :
    system.map (homOfLE (n.le_add_right 1)) ≫ spaceι (n + 1) =
      spaceι n ≫ ((Functor.const ℕ).obj spaceColimit).map (homOfLE (n.le_add_right 1)) :=
  sorry

/-- The sequential cocone on `system` with apex `spaceColimit`. -/
def spaceCocone : Cocone system where
  pt := spaceColimit
  ι := NatTrans.ofSequence spaceι spaceι_naturality

/-- The space-colimit topology does not make `colimitCarrier` a topological group. -/
theorem not_isTopologicalAddGroup_spaceColimitTopology :
    ¬ @IsTopologicalAddGroup colimitCarrier spaceColimitTopology _ :=
  sorry

/-- The specified space cocone satisfies the categorical colimit universal property. -/
theorem nonempty_isColimit_spaceCocone : Nonempty (IsColimit spaceCocone) :=
  sorry

/-- The final space topology and the finest admissible additive group topology differ
on the rational-times-finite-support real carrier. -/
theorem spaceColimitTopology_ne_groupColimitTopology :
    spaceColimitTopology ≠ groupColimitTopology.toTopologicalSpace :=
  sorry

end

end TopCat.Counterexample.NatAddGroupColimit
