/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import ReasLib.CategoryTheory.Sites.Family
public import ReasLib.CategoryTheory.Sites.Family.BaseChange
public import Mathlib.CategoryTheory.Sites.Precoverage

/-!
# Covering predicates on fixed-target families

Predicates characterizing when a fixed-target family covers, refines another,
or is equivalent in combinatorial or tautological sense.  Combinatorial
equivalence controls presieves; tautological equivalence controls only their
generated sieves.
-/

@[expose] public section

universe w₃ w₂ w₁ w v u

namespace CategoryTheory
namespace SemiRepresentableFamily.Over

variable {C : Type u} [Category.{v} C] {U : C}

/-- Reindex a finite fixed-target family by the canonical finite type
`Fin (Nat.card 𝒰.index)`.  This removes an arbitrary finite indexing universe
without changing the arrows in the family. -/
/- no direct Stacks tag: this is a finite reindexing adapter. -/
noncomputable def finReindex (𝒰 : Over.{w} U) [Finite 𝒰.index] : Over.{0} U where
  index := Fin (Nat.card 𝒰.index)
  obj := fun i => 𝒰.obj ((Finite.equivFin 𝒰.index).symm i)

/-- Canonical finite reindexing preserves the generated presieve. -/
@[simp]
theorem finReindex_toPresieve (𝒰 : Over.{w} U) [Finite 𝒰.index] :
    (finReindex 𝒰).toPresieve = 𝒰.toPresieve := by
  exact Presieve.ofArrows_comp_eq_of_surjective
    (fun i ↦ (𝒰.obj i).hom) (Finite.equivFin 𝒰.index).symm.surjective

/-- Canonical finite reindexing preserves the generated sieve. -/
@[simp]
theorem finReindex_toSieve (𝒰 : Over.{w} U) [Finite 𝒰.index] :
    (finReindex 𝒰).toSieve = 𝒰.toSieve := by
  exact congrArg Sieve.generate (finReindex_toPresieve 𝒰)

/-- The canonical finite reindexing has finite index type. -/
/- no direct Stacks tag: this is a finite reindexing adapter. -/
instance finite_finReindex_index (𝒰 : Over.{w} U) [Finite 𝒰.index] :
    Finite (finReindex 𝒰).index := by
  change Finite (Fin (Nat.card 𝒰.index))
  infer_instance

/-- A fixed-target family is covering for a precoverage when its generated presieve belongs
to that precoverage. -/
/- no direct Stacks tag: the covering predicate is a Mathlib precoverage bridge. -/
abbrev IsCovering (K : Precoverage C) (𝒰 : Over.{w} U) : Prop :=
  toPresieve 𝒰 ∈ K U

/-- For the precoverage associated to a Grothendieck topology, covering a fixed-target family
is exactly covering of its generated sieve.  This bridge keeps the family API aligned with the
site-level `J U` notation used by descent and inherited-topology consumers. -/
@[simp]
theorem isCovering_toPrecoverage_iff
    (J : GrothendieckTopology C) (𝒰 : Over.{w} U) :
    IsCovering J.toPrecoverage 𝒰 ↔ 𝒰.toSieve ∈ J U := Iff.rfl

/-- Componentwise base change of a covering fixed-target family is covering. -/
/- no direct Stacks tag: this specializes the site base-change axiom. -/
theorem baseChange_toSieve_mem {V : C} {J : GrothendieckTopology C}
    (𝒰 : Over.{w} U) (f : V ⟶ U)
    [∀ i : 𝒰.index, Limits.HasPullback (𝒰.obj i).hom f]
    (h𝒰 : 𝒰.toSieve ∈ J U) :
    (𝒰.baseChange f).toSieve ∈ J V := by
  have h : (𝒰.baseChange f).toSieve = 𝒰.toSieve.pullback f :=
    Sieve.ofArrows_eq_pullback_of_isPullback (fun i ↦ (𝒰.obj i).hom)
      (fun i ↦ (IsPullback.of_hasPullback (𝒰.obj i).hom f).flip)
  rw [h]
  exact J.pullback_stable f h𝒰

/-- Componentwise base change preserves covering families for every precoverage stable under
base change.  This is the neutral owner; a Grothendieck topology is used through its canonical
`toPrecoverage` instance. -/
/- no direct Stacks tag: this specializes the precoverage base-change axiom. -/
theorem IsCovering.baseChange {V : C} {K : Precoverage C} [K.IsStableUnderBaseChange]
    {𝒰 : Over.{w} U} (h𝒰 : IsCovering K 𝒰) (f : V ⟶ U)
    [∀ i : 𝒰.index, Limits.HasPullback (𝒰.obj i).hom f] :
    IsCovering K (𝒰.baseChange f) := by
  exact Precoverage.mem_coverings_of_isPullback (fun i ↦ (𝒰.obj i).hom) h𝒰 f
    (fun i ↦ Limits.pullback.snd (𝒰.obj i).hom f)
    (fun i ↦ Limits.pullback.fst (𝒰.obj i).hom f)
    (fun i ↦ (IsPullback.of_hasPullback (𝒰.obj i).hom f).flip)

/-- A family `𝒰` refines `𝒱` when there exists a componentwise reindexing map from `𝒰` to
`𝒱`.  The two index types may live in different universes; the homogeneous category notation is
recovered by specializing both levels to the same `w`. -/
@[stacks 00VT "family refinement"]
abbrev Refines (𝒰 : Over.{w₁} U) (𝒱 : Over.{w₂} U) : Prop :=
  Nonempty (SemiRepresentableFamily.Over.Hom 𝒰 𝒱)

/-- Two fixed-target families mutually refine one another, allowing independent index universes. -/
/- The mutual relation is recorded by the 00VV equivalence theorem below. -/
def MutuallyRefines (𝒰 : Over.{w₁} U) (𝒱 : Over.{w₂} U) : Prop :=
  Refines 𝒰 𝒱 ∧ Refines 𝒱 𝒰

private theorem toSieve_le_of_hom {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (f : SemiRepresentableFamily.Over.Hom 𝒰 𝒱) : 𝒰.toSieve ≤ 𝒱.toSieve := by
  apply (Sieve.generate_le_iff _ _).2
  rintro X k ⟨i⟩
  rw [← CategoryTheory.Over.w (f.f i)]
  exact 𝒱.toSieve.downward_closed
    (Sieve.le_generate _ _ _ (Presieve.ofArrows.mk (f.α i))) (f.f i).left

/-- Refinement is exactly the nonemptiness of the canonical hom type. -/
/- This is a definitional bridge to the family category. -/
theorem refines_iff_nonempty_hom {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U} :
    Refines 𝒰 𝒱 ↔ Nonempty (SemiRepresentableFamily.Over.Hom 𝒰 𝒱) := Iff.rfl

/-- Two fixed-target families are combinatorially equivalent when their displayed arrows agree
after reindexing in both directions. The index universes may differ. Equality of generated
presieves is strictly weaker and is exposed only as a consequence. -/
@[stacks 00VU "combinatorial family equivalence"]
def CombinatoriallyEquivalent (𝒰 : Over.{w₁} U) (𝒱 : Over.{w₂} U) : Prop :=
  ∃ α : 𝒰.index → 𝒱.index, ∃ β : 𝒱.index → 𝒰.index,
    (∀ i : 𝒰.index, 𝒰.obj i = 𝒱.obj (α i)) ∧
      ∀ j : 𝒱.index, 𝒱.obj j = 𝒰.obj (β j)

/-- Two families are tautologically equivalent if they admit reindexings in both directions
whose component maps are isomorphisms in the slice.  The index universes may differ. -/
@[stacks 00VU "tautological family equivalence"]
def TautologicallyEquivalent (𝒰 : Over.{w₁} U) (𝒱 : Over.{w₂} U) : Prop :=
  ∃ f : SemiRepresentableFamily.Over.Hom 𝒰 𝒱,
    ∃ g : SemiRepresentableFamily.Over.Hom 𝒱 𝒰,
    (∀ i : 𝒰.index, IsIso (f.f i)) ∧ ∀ j : 𝒱.index, IsIso (g.f j)

/-- The componentwise reindexing specification for combinatorial equivalence. -/
@[stacks 00VU "combinatorial equivalence specification"]
theorem combinatoriallyEquivalent_iff_exists_reindexings
    {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U} :
    CombinatoriallyEquivalent 𝒰 𝒱 ↔
      ∃ α : 𝒰.index → 𝒱.index, ∃ β : 𝒱.index → 𝒰.index,
        (∀ i : 𝒰.index, 𝒰.obj i = 𝒱.obj (α i)) ∧
          ∀ j : 𝒱.index, 𝒱.obj j = 𝒰.obj (β j) := Iff.rfl

private theorem toPresieve_eq_of_combinatoriallyEquivalent
    {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (h : CombinatoriallyEquivalent 𝒰 𝒱) : 𝒰.toPresieve = 𝒱.toPresieve := by
  rcases h with ⟨α, β, hα, hβ⟩
  apply le_antisymm
  · rintro X k ⟨i⟩
    rw [hα i]
    exact Presieve.ofArrows.mk (α i)
  · rintro X k ⟨j⟩
    rw [hβ j]
    exact Presieve.ofArrows.mk (β j)

/-- Combinatorially equivalent families admit tautological reindexings. -/
@[stacks 00VV "combinatorial-to-tautological equivalence"]
theorem CombinatoriallyEquivalent.toTautologicallyEquivalent
    {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (h : CombinatoriallyEquivalent 𝒰 𝒱) : TautologicallyEquivalent 𝒰 𝒱 := by
  rcases h with ⟨α, β, hα, hβ⟩
  refine ⟨⟨α, fun i ↦ eqToHom (hα i)⟩, ⟨β, fun j ↦ eqToHom (hβ j)⟩, ?_, ?_⟩
  · intro i
    change IsIso (eqToHom (hα i))
    infer_instance
  · intro j
    change IsIso (eqToHom (hβ j))
    infer_instance

/-- Combinatorial equivalence is reflexive. -/
theorem CombinatoriallyEquivalent.refl (𝒰 : Over.{w} U) :
    CombinatoriallyEquivalent 𝒰 𝒰 :=
  ⟨id, id, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- Combinatorial equivalence is symmetric. -/
theorem CombinatoriallyEquivalent.symm {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (h : CombinatoriallyEquivalent 𝒰 𝒱) : CombinatoriallyEquivalent 𝒱 𝒰 := by
  rcases h with ⟨α, β, hα, hβ⟩
  exact ⟨β, α, hβ, hα⟩

/-- Combinatorial equivalence is transitive. -/
theorem CombinatoriallyEquivalent.trans
    {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U} {𝒲 : Over.{w₃} U}
    (h₁ : CombinatoriallyEquivalent 𝒰 𝒱) (h₂ : CombinatoriallyEquivalent 𝒱 𝒲) :
    CombinatoriallyEquivalent 𝒰 𝒲 := by
  rcases h₁ with ⟨α₁, β₁, hα₁, hβ₁⟩
  rcases h₂ with ⟨α₂, β₂, hα₂, hβ₂⟩
  exact ⟨α₂ ∘ α₁, β₁ ∘ β₂,
    fun i ↦ (hα₁ i).trans (hα₂ (α₁ i)),
    fun j ↦ (hβ₂ j).trans (hβ₁ (β₂ j))⟩

/-- Combinatorial equivalence is an equivalence relation on fixed-target families. -/
@[stacks 00VV "combinatorial equivalence relation"]
theorem CombinatoriallyEquivalent.isEquivalence :
    _root_.Equivalence
      (CombinatoriallyEquivalent : Over.{w} U → Over.{w} U → Prop) :=
  ⟨CombinatoriallyEquivalent.refl, CombinatoriallyEquivalent.symm,
    CombinatoriallyEquivalent.trans⟩

/-- Combinatorially equivalent families have the same covering status. -/
theorem IsCovering.of_combinatoriallyEquivalent {K : Precoverage C}
    {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (h : CombinatoriallyEquivalent 𝒰 𝒱) (hc : IsCovering K 𝒰) : IsCovering K 𝒱 := by
  change 𝒱.toPresieve ∈ K U
  rw [← toPresieve_eq_of_combinatoriallyEquivalent h]
  exact hc

/-- Two covering fixed-target families admit a common covering refinement. -/
@[stacks 00W6 "common covering refinement"]
theorem existsCommonCoveringRefinement
    {J : Precoverage C} [J.HasPullbacks] [J.IsStableUnderBaseChange]
    [J.IsStableUnderComposition] (𝒰 𝒱 : Over.{w} U)
    (h𝒰 : IsCovering J 𝒰) (h𝒱 : IsCovering J 𝒱) :
    ∃ 𝒲 : Over.{w} U, IsCovering J 𝒲 ∧ Refines 𝒲 𝒰 ∧ Refines 𝒲 𝒱 := by
  letI (i : 𝒰.index) : 𝒱.toPresieve.HasPullbacks (𝒰.obj i).hom :=
    Precoverage.hasPullbacks_of_mem (𝒰.obj i).hom h𝒱
  letI (i : 𝒰.index) (j : 𝒱.index) :
      Limits.HasPullback (𝒱.obj j).hom (𝒰.obj i).hom :=
    Presieve.hasPullback (R := 𝒱.toPresieve) (𝒰.obj i).hom (Presieve.ofArrows.mk j)
  let 𝒲 := 𝒰.bind (fun i ↦ 𝒱.baseChange (𝒰.obj i).hom)
  refine ⟨𝒲, ?_, ?_, ?_⟩
  · exact Precoverage.comp_mem_coverings (fun i ↦ (𝒰.obj i).hom) h𝒰
      (fun i j ↦ Limits.pullback.snd (𝒱.obj j).hom (𝒰.obj i).hom)
      (fun i ↦ h𝒱.baseChange (𝒰.obj i).hom)
  · refine ⟨⟨(fun ij ↦ ij.1), fun ij ↦ ?_⟩⟩
    exact CategoryTheory.Over.homMk
      (Limits.pullback.snd (𝒱.obj ij.2).hom (𝒰.obj ij.1).hom) rfl
  · refine ⟨⟨(fun ij ↦ ij.2), fun ij ↦ ?_⟩⟩
    exact CategoryTheory.Over.homMk
      (Limits.pullback.fst (𝒱.obj ij.2).hom (𝒰.obj ij.1).hom)
      Limits.pullback.condition

/-- Combinatorially equivalent families generate the same presieve. -/
@[stacks 00VU "presieve invariance under combinatorial equivalence"]
theorem CombinatoriallyEquivalent.toPresieve_eq
    {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (h : CombinatoriallyEquivalent 𝒰 𝒱) : toPresieve 𝒰 = toPresieve 𝒱 :=
  toPresieve_eq_of_combinatoriallyEquivalent h

/-- Combinatorially equivalent families generate the same sieve. -/
theorem CombinatoriallyEquivalent.toSieve_eq
    {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (h : CombinatoriallyEquivalent 𝒰 𝒱) : toSieve 𝒰 = toSieve 𝒱 :=
  congrArg Sieve.generate h.toPresieve_eq

/-- Tautological equivalence gives a refinement in its forward direction. -/
theorem TautologicallyEquivalent.refines {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (h : TautologicallyEquivalent 𝒰 𝒱) : Refines 𝒰 𝒱 := by
  rcases h with ⟨f, _, _, _⟩
  exact ⟨f⟩

/-- Tautological equivalence gives mutual refinement. -/
theorem TautologicallyEquivalent.mutuallyRefines
    {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (h : TautologicallyEquivalent 𝒰 𝒱) : MutuallyRefines 𝒰 𝒱 := by
  rcases h with ⟨f, g, _, _⟩
  exact ⟨⟨f⟩, ⟨g⟩⟩

/-- Tautological equivalence is reflexive. -/
theorem TautologicallyEquivalent.refl (𝒰 : Over.{w} U) :
    TautologicallyEquivalent 𝒰 𝒰 := by
  refine ⟨Hom.id 𝒰, Hom.id 𝒰, ?_, ?_⟩
  · intro i
    change IsIso (𝟙 (𝒰.obj i))
    infer_instance
  · intro i
    change IsIso (𝟙 (𝒰.obj i))
    infer_instance

/-- Tautological equivalence is symmetric. -/
theorem TautologicallyEquivalent.symm {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (h : TautologicallyEquivalent 𝒰 𝒱) : TautologicallyEquivalent 𝒱 𝒰 := by
  rcases h with ⟨f, g, hf, hg⟩
  exact ⟨g, f, hg, hf⟩

/-- Tautological equivalence is transitive. -/
theorem TautologicallyEquivalent.trans
    {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U} {𝒲 : Over.{w₃} U}
    (h₁ : TautologicallyEquivalent 𝒰 𝒱) (h₂ : TautologicallyEquivalent 𝒱 𝒲) :
    TautologicallyEquivalent 𝒰 𝒲 := by
  rcases h₁ with ⟨f₁, g₁, hf₁, hg₁⟩
  rcases h₂ with ⟨f₂, g₂, hf₂, hg₂⟩
  refine ⟨Hom.comp f₁ f₂, Hom.comp g₂ g₁, ?_, ?_⟩
  · intro i
    letI := hf₁ i
    letI := hf₂ (f₁.α i)
    change IsIso (f₁.f i ≫ f₂.f (f₁.α i))
    infer_instance
  · intro j
    letI := hg₂ j
    letI := hg₁ (g₂.α j)
    change IsIso (g₂.f j ≫ g₁.f (g₂.α j))
    infer_instance

/-- Tautological equivalence is an equivalence relation on fixed-target families. -/
@[stacks 00VV "tautological equivalence relation"]
theorem TautologicallyEquivalent.isEquivalence :
    _root_.Equivalence
      (TautologicallyEquivalent : Over.{w} U → Over.{w} U → Prop) :=
  ⟨TautologicallyEquivalent.refl, TautologicallyEquivalent.symm,
    TautologicallyEquivalent.trans⟩

/-- Tautologically equivalent families generate the same sieve.  This does not,
in general, imply equality of their generated presieves. -/
theorem TautologicallyEquivalent.toSieve_eq
    {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (h : TautologicallyEquivalent 𝒰 𝒱) : toSieve 𝒰 = toSieve 𝒱 := by
  rcases h with ⟨f, g, _, _⟩
  exact le_antisymm (toSieve_le_of_hom f) (toSieve_le_of_hom g)

/-- A refinement generates a sieve contained in the sieve generated by the coarser family. -/
@[stacks 00VT "sieve monotonicity under refinement"]
theorem Refines.toSieve_le {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (h : Refines 𝒰 𝒱) : toSieve 𝒰 ≤ toSieve 𝒱 := by
  rcases h with ⟨f⟩
  exact toSieve_le_of_hom f

/-- Refinement is reflexive. -/
theorem Refines.refl (𝒰 : Over.{w} U) : Refines 𝒰 𝒰 := ⟨Hom.id 𝒰⟩

/-- Refinement is transitive. -/
theorem Refines.trans
    {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U} {𝒲 : Over.{w₃} U}
    (h₁ : Refines 𝒰 𝒱) (h₂ : Refines 𝒱 𝒲) : Refines 𝒰 𝒲 := by
  rcases h₁ with ⟨f⟩
  rcases h₂ with ⟨g⟩
  exact ⟨Hom.comp f g⟩

/-- Mutual refinement is reflexive. -/
theorem MutuallyRefines.refl (𝒰 : Over.{w} U) : MutuallyRefines 𝒰 𝒰 :=
  ⟨Refines.refl 𝒰, Refines.refl 𝒰⟩

/-- Mutual refinement is symmetric. -/
theorem MutuallyRefines.symm {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (h : MutuallyRefines 𝒰 𝒱) : MutuallyRefines 𝒱 𝒰 := ⟨h.2, h.1⟩

/-- Mutual refinement is transitive. -/
theorem MutuallyRefines.trans
    {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U} {𝒲 : Over.{w₃} U}
    (h₁ : MutuallyRefines 𝒰 𝒱) (h₂ : MutuallyRefines 𝒱 𝒲) :
    MutuallyRefines 𝒰 𝒲 :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

/-- Mutually refining families generate the same sieve. -/
@[stacks 00VV "sieve invariance under mutual refinement"]
theorem MutuallyRefines.toSieve_eq {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (h : MutuallyRefines 𝒰 𝒱) : toSieve 𝒰 = toSieve 𝒱 :=
  le_antisymm h.1.toSieve_le h.2.toSieve_le

/-- Mutual refinement is an equivalence relation on fixed-target families. -/
@[stacks 00VV "mutual refinement equivalence relation"]
theorem MutuallyRefines.isEquivalence :
    _root_.Equivalence (MutuallyRefines : Over.{w} U → Over.{w} U → Prop) :=
  ⟨MutuallyRefines.refl, MutuallyRefines.symm, MutuallyRefines.trans⟩


end SemiRepresentableFamily.Over
end CategoryTheory
