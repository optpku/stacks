/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Category.LCCat.Limits
public import ReasLib.CategoryTheory.Sites.Family.BaseChange
public import ReasLib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Quasi-compact covering families in `LCCat`

The covering condition is a predicate on the canonical fixed-target family owner
`SemiRepresentableFamily.Over X`.  Indexed arrows are retained only as an input presentation;
composition and base change are expressed directly on that owner.
-/

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open Set Topology

universe u v w

namespace CategoryTheory.SemiRepresentableFamily.Over

variable {X : LCCat.{u}}

/-- Definition 21.31.2 (09X0): a fixed-target family in `LCCat` is a qc covering if every
point has a neighborhood contained in finitely many images of compact source subsets. -/
@[stacks 09X0]
def IsQuasiCompactCovering (𝒰 : Over X) : Prop :=
  ∀ x : X.obj, ∃ s : Finset 𝒰.index, ∃ E : ∀ i : s, Set ((𝒰.obj i.1).left.obj),
    (∀ i : s, IsCompact (E i)) ∧ (⋃ i : s, (𝒰.obj i.1).hom '' E i) ∈ 𝓝 x

namespace IsQuasiCompactCovering

/-- A qc covering supplies its finite compact-image neighborhood at a chosen point. -/
@[stacks 09X0 "finite compact-image neighborhood from a qc covering"]
theorem exists_compact_image_mem_nhds
    {𝒰 : Over X} (h : 𝒰.IsQuasiCompactCovering) (x : X.obj) :
    ∃ s : Finset 𝒰.index, ∃ E : ∀ i : s, Set ((𝒰.obj i.1).left.obj),
      (∀ i : s, IsCompact (E i)) ∧ (⋃ i : s, (𝒰.obj i.1).hom '' E i) ∈ 𝓝 x := sorry

/-- A qc covering supplies an open neighborhood inside a finite compact-image union. -/
@[stacks 09X0 "open neighborhood inside a qc compact-image union"]
theorem exists_open_subset_compact_image
    {𝒰 : Over X} (h : 𝒰.IsQuasiCompactCovering) (x : X.obj) :
    ∃ s : Finset 𝒰.index, ∃ E : ∀ i : s, Set ((𝒰.obj i.1).left.obj), ∃ V : Set X.obj,
      (∀ i : s, IsCompact (E i)) ∧ IsOpen V ∧ x ∈ V ∧
        V ⊆ ⋃ i : s, (𝒰.obj i.1).hom '' E i := sorry

/-- The owner predicate specializes to the textbook indexed-arrow formulation. -/
@[stacks 09X0 "indexed qc-covering criterion"]
theorem ofArrows_iff {I : Type v} (X_ : I → LCCat.{u}) (f : ∀ i, X_ i ⟶ X) :
    (ofArrows X_ f).IsQuasiCompactCovering ↔
      ∀ x : X.obj, ∃ s : Finset I, ∃ E : ∀ i : s, Set ((X_ i.1).obj),
        (∀ i : s, IsCompact (E i)) ∧ (⋃ i : s, f i.1 '' E i) ∈ 𝓝 x := sorry

/-- Lemma 21.31.3 (09X1), clause (1): an isomorphism gives a singleton qc covering. -/
@[stacks 09X1 "(1)"]
theorem singleton_of_isIso {X' : LCCat.{u}} (f : X' ⟶ X) [IsIso f] :
    (singleton f).IsQuasiCompactCovering := sorry

/-- Lemma 21.31.3 (09X1), clause (2): a qc family bound to qc families is qc. -/
@[stacks 09X1 "(2)"]
theorem bind {𝒰 : Over.{v} X}
    (𝒱 : ∀ i : 𝒰.index, Over.{w} (𝒰.obj i).left)
    (h𝒰 : 𝒰.IsQuasiCompactCovering)
    (h𝒱 : ∀ i, (𝒱 i).IsQuasiCompactCovering) :
    (𝒰.bind 𝒱).IsQuasiCompactCovering := sorry

/-- The indexed-arrow presentation of closure of qc coverings under composition. -/
@[stacks 09X1 "(2), indexed presentation"]
theorem ofArrows_bind {I : Type v} {J : I → Type w} {X_ : I → LCCat.{u}}
    {f : ∀ i, X_ i ⟶ X} {X__ : ∀ i, J i → LCCat.{u}}
    (g : ∀ i j, X__ i j ⟶ X_ i)
    (hf : (ofArrows X_ f).IsQuasiCompactCovering)
    (hg : ∀ i, (ofArrows (X__ i) (g i)).IsQuasiCompactCovering) :
    ((ofArrows X_ f).bind (fun i ↦ ofArrows (X__ i) (g i))).IsQuasiCompactCovering := sorry

/-- Lemma 21.31.3 (09X1), clause (3): qc coverings are stable under base change. -/
@[stacks 09X1 "(3)"]
theorem baseChange {X' : LCCat.{u}} {𝒰 : Over X}
    (h𝒰 : 𝒰.IsQuasiCompactCovering) (φ : X' ⟶ X) :
    (𝒰.baseChange φ).IsQuasiCompactCovering := sorry

/-- Any displayed pullback family of a qc covering is again a qc covering. -/
@[stacks 09X1 "pullback presentation of a qc covering"]
theorem of_isPullback {I : Type v} {Y : LCCat.{u}} {X_ : I → LCCat.{u}}
    (f : ∀ i, X_ i ⟶ X) (hf : (ofArrows X_ f).IsQuasiCompactCovering)
    (g : Y ⟶ X) {Q : I → LCCat.{u}}
    (p₁ : ∀ i, Q i ⟶ Y) (p₂ : ∀ i, Q i ⟶ X_ i)
    (hpb : ∀ i, IsPullback (p₁ i) (p₂ i) g (f i)) :
    (ofArrows Q p₁).IsQuasiCompactCovering := sorry

/-- A singleton is qc covering exactly when every point has a compact-image neighborhood. -/
@[stacks 09X1 "singleton qc covering criterion"]
theorem singleton_iff {Y : LCCat.{u}} (f : X ⟶ Y) :
    (singleton f).IsQuasiCompactCovering ↔
      ∀ y : Y.obj, ∃ K : Set X.obj, IsCompact K ∧ f '' K ∈ 𝓝 y := sorry

/-- Lemma 21.31.4 (09X5): a proper surjective morphism gives a singleton qc covering. -/
@[stacks 09X5]
theorem singleton_of_proper_surjective {Y : LCCat.{u}} (f : X ⟶ Y)
    (hf : IsProperMap f) (hsurj : Function.Surjective f) :
    (singleton f).IsQuasiCompactCovering := sorry

end IsQuasiCompactCovering

end CategoryTheory.SemiRepresentableFamily.Over

namespace LCCat

/-- Lemma 21.31.9: the morphism property of proper maps in `LCCat`. -/
@[stacks 0EZI "proper morphisms in LC"]
abbrev proper : MorphismProperty LCCat.{u} :=
  fun _ _ f ↦ IsProperMap f.hom

/-- Lemma 21.31.9 (1): proper morphisms in `LCCat` admit pullbacks. -/
@[stacks 0EZI "(1)"]
theorem proper_hasPullbacks : MorphismProperty.HasPullbacks proper := sorry

/-- Lemma 21.31.9 (2): proper morphisms in `LCCat` are stable under base change. -/
@[stacks 0EZI "(2)"]
theorem proper_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange proper := sorry

/-- The reusable pullback instance for the proper morphism property. -/
@[stacks 0EZI "proper pullbacks", instance]
instance proper_hasPullbacks_instance : MorphismProperty.HasPullbacks proper :=
  proper_hasPullbacks

/-- The reusable base-change instance for the proper morphism property. -/
@[stacks 0EZI "proper base change", instance]
instance proper_isStableUnderBaseChange_instance :
    MorphismProperty.IsStableUnderBaseChange proper :=
  proper_isStableUnderBaseChange

end LCCat

end
