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
    (finReindex 𝒰).toPresieve = 𝒰.toPresieve := sorry

/-- Canonical finite reindexing preserves the generated sieve. -/
@[simp]
theorem finReindex_toSieve (𝒰 : Over.{w} U) [Finite 𝒰.index] :
    (finReindex 𝒰).toSieve = 𝒰.toSieve := sorry

/-- The canonical finite reindexing has finite index type. -/
/- no direct Stacks tag: this is a finite reindexing adapter. -/
instance finite_finReindex_index (𝒰 : Over.{w} U) [Finite 𝒰.index] :
    Finite (finReindex 𝒰).index := sorry

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
    IsCovering J.toPrecoverage 𝒰 ↔ 𝒰.toSieve ∈ J U := sorry

/-- Componentwise base change of a covering fixed-target family is covering. -/
/- no direct Stacks tag: this specializes the site base-change axiom. -/
theorem baseChange_toSieve_mem {V : C} {J : GrothendieckTopology C}
    (𝒰 : Over.{w} U) (f : V ⟶ U)
    [∀ i : 𝒰.index, Limits.HasPullback (𝒰.obj i).hom f]
    (h𝒰 : 𝒰.toSieve ∈ J U) :
    (𝒰.baseChange f).toSieve ∈ J V := sorry

/-- Componentwise base change preserves covering families for every precoverage stable under
base change.  This is the neutral owner; a Grothendieck topology is used through its canonical
`toPrecoverage` instance. -/
/- no direct Stacks tag: this specializes the precoverage base-change axiom. -/
theorem IsCovering.baseChange {V : C} {K : Precoverage C} [K.IsStableUnderBaseChange]
    {𝒰 : Over.{w} U} (h𝒰 : IsCovering K 𝒰) (f : V ⟶ U)
    [∀ i : 𝒰.index, Limits.HasPullback (𝒰.obj i).hom f] :
    IsCovering K (𝒰.baseChange f) := sorry

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

/-- Refinement is exactly the nonemptiness of the canonical hom type. -/
/- This is a definitional bridge to the family category. -/
theorem refines_iff_nonempty_hom {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U} :
    Refines 𝒰 𝒱 ↔ Nonempty (SemiRepresentableFamily.Over.Hom 𝒰 𝒱) := sorry

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
          ∀ j : 𝒱.index, 𝒱.obj j = 𝒰.obj (β j) := sorry

/-- Combinatorially equivalent families admit tautological reindexings. -/
@[stacks 00VV "combinatorial-to-tautological equivalence"]
theorem CombinatoriallyEquivalent.toTautologicallyEquivalent
    {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (h : CombinatoriallyEquivalent 𝒰 𝒱) : TautologicallyEquivalent 𝒰 𝒱 := sorry

/-- Combinatorial equivalence is reflexive. -/
theorem CombinatoriallyEquivalent.refl (𝒰 : Over.{w} U) :
    CombinatoriallyEquivalent 𝒰 𝒰 := sorry

/-- Combinatorial equivalence is symmetric. -/
theorem CombinatoriallyEquivalent.symm {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (h : CombinatoriallyEquivalent 𝒰 𝒱) : CombinatoriallyEquivalent 𝒱 𝒰 := sorry

/-- Combinatorial equivalence is transitive. -/
theorem CombinatoriallyEquivalent.trans
    {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U} {𝒲 : Over.{w₃} U}
    (h₁ : CombinatoriallyEquivalent 𝒰 𝒱) (h₂ : CombinatoriallyEquivalent 𝒱 𝒲) :
    CombinatoriallyEquivalent 𝒰 𝒲 := sorry

/-- Combinatorial equivalence is an equivalence relation on fixed-target families. -/
@[stacks 00VV "combinatorial equivalence relation"]
theorem CombinatoriallyEquivalent.isEquivalence :
    _root_.Equivalence
      (CombinatoriallyEquivalent : Over.{w} U → Over.{w} U → Prop) := sorry

/-- Combinatorially equivalent families have the same covering status. -/
theorem IsCovering.of_combinatoriallyEquivalent {K : Precoverage C}
    {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (h : CombinatoriallyEquivalent 𝒰 𝒱) (hc : IsCovering K 𝒰) : IsCovering K 𝒱 := sorry

/-- Two covering fixed-target families admit a common covering refinement. -/
@[stacks 00W6 "common covering refinement"]
theorem existsCommonCoveringRefinement
    {J : Precoverage C} [J.HasPullbacks] [J.IsStableUnderBaseChange]
    [J.IsStableUnderComposition] (𝒰 𝒱 : Over.{w} U)
    (h𝒰 : IsCovering J 𝒰) (h𝒱 : IsCovering J 𝒱) :
    ∃ 𝒲 : Over.{w} U, IsCovering J 𝒲 ∧ Refines 𝒲 𝒰 ∧ Refines 𝒲 𝒱 := sorry

/-- Combinatorially equivalent families generate the same presieve. -/
@[stacks 00VU "presieve invariance under combinatorial equivalence"]
theorem CombinatoriallyEquivalent.toPresieve_eq
    {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (h : CombinatoriallyEquivalent 𝒰 𝒱) : toPresieve 𝒰 = toPresieve 𝒱 := sorry

/-- Combinatorially equivalent families generate the same sieve. -/
theorem CombinatoriallyEquivalent.toSieve_eq
    {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (h : CombinatoriallyEquivalent 𝒰 𝒱) : toSieve 𝒰 = toSieve 𝒱 := sorry

/-- Tautological equivalence gives a refinement in its forward direction. -/
theorem TautologicallyEquivalent.refines {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (h : TautologicallyEquivalent 𝒰 𝒱) : Refines 𝒰 𝒱 := sorry

/-- Tautological equivalence gives mutual refinement. -/
theorem TautologicallyEquivalent.mutuallyRefines
    {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (h : TautologicallyEquivalent 𝒰 𝒱) : MutuallyRefines 𝒰 𝒱 := sorry

/-- Tautological equivalence is reflexive. -/
theorem TautologicallyEquivalent.refl (𝒰 : Over.{w} U) :
    TautologicallyEquivalent 𝒰 𝒰 := sorry

/-- Tautological equivalence is symmetric. -/
theorem TautologicallyEquivalent.symm {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (h : TautologicallyEquivalent 𝒰 𝒱) : TautologicallyEquivalent 𝒱 𝒰 := sorry

/-- Tautological equivalence is transitive. -/
theorem TautologicallyEquivalent.trans
    {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U} {𝒲 : Over.{w₃} U}
    (h₁ : TautologicallyEquivalent 𝒰 𝒱) (h₂ : TautologicallyEquivalent 𝒱 𝒲) :
    TautologicallyEquivalent 𝒰 𝒲 := sorry

/-- Tautological equivalence is an equivalence relation on fixed-target families. -/
@[stacks 00VV "tautological equivalence relation"]
theorem TautologicallyEquivalent.isEquivalence :
    _root_.Equivalence
      (TautologicallyEquivalent : Over.{w} U → Over.{w} U → Prop) := sorry

/-- Tautologically equivalent families generate the same sieve.  This does not,
in general, imply equality of their generated presieves. -/
theorem TautologicallyEquivalent.toSieve_eq
    {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (h : TautologicallyEquivalent 𝒰 𝒱) : toSieve 𝒰 = toSieve 𝒱 := sorry

/-- A refinement generates a sieve contained in the sieve generated by the coarser family. -/
@[stacks 00VT "sieve monotonicity under refinement"]
theorem Refines.toSieve_le {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (h : Refines 𝒰 𝒱) : toSieve 𝒰 ≤ toSieve 𝒱 := sorry

/-- Refinement is reflexive. -/
theorem Refines.refl (𝒰 : Over.{w} U) : Refines 𝒰 𝒰 := sorry

/-- Refinement is transitive. -/
theorem Refines.trans
    {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U} {𝒲 : Over.{w₃} U}
    (h₁ : Refines 𝒰 𝒱) (h₂ : Refines 𝒱 𝒲) : Refines 𝒰 𝒲 := sorry

/-- Mutual refinement is reflexive. -/
theorem MutuallyRefines.refl (𝒰 : Over.{w} U) : MutuallyRefines 𝒰 𝒰 := sorry

/-- Mutual refinement is symmetric. -/
theorem MutuallyRefines.symm {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (h : MutuallyRefines 𝒰 𝒱) : MutuallyRefines 𝒱 𝒰 := sorry

/-- Mutual refinement is transitive. -/
theorem MutuallyRefines.trans
    {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U} {𝒲 : Over.{w₃} U}
    (h₁ : MutuallyRefines 𝒰 𝒱) (h₂ : MutuallyRefines 𝒱 𝒲) :
    MutuallyRefines 𝒰 𝒲 := sorry

/-- Mutually refining families generate the same sieve. -/
@[stacks 00VV "sieve invariance under mutual refinement"]
theorem MutuallyRefines.toSieve_eq {𝒰 : Over.{w₁} U} {𝒱 : Over.{w₂} U}
    (h : MutuallyRefines 𝒰 𝒱) : toSieve 𝒰 = toSieve 𝒱 := sorry

/-- Mutual refinement is an equivalence relation on fixed-target families. -/
@[stacks 00VV "mutual refinement equivalence relation"]
theorem MutuallyRefines.isEquivalence :
    _root_.Equivalence (MutuallyRefines : Over.{w} U → Over.{w} U → Prop) := sorry


end SemiRepresentableFamily.Over
end CategoryTheory
