module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Set.Restrict
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace TopCat.Presheaf.PointwiseProduct

variable {X : TopCat.{u}}

/-- A restriction-compatible family of subgroups of pointwise products on a topological
basis. -/
structure BasisSubgroups {X : TopCat.{u}} (A : X → AddCommGrpCat.{u}) where
  basis : Set (Opens X)
  isBasis : Opens.IsBasis basis
  subgroup : ∀ U, U ∈ basis → AddSubgroup (∀ x : U, A x)
  compatible : ∀ {U V} (hU : U ∈ basis) (hV : V ∈ basis) (hUV : U ≤ V)
      {s : ∀ x : V, A x}, s ∈ subgroup V hV → Set.restrict₂ (π := fun x ↦ A x) hUV s ∈ subgroup U hU

namespace BasisSubgroups

/-- The family of full pointwise product groups on a basis. -/
def top (A : X → AddCommGrpCat.{u}) {B : Set (Opens X)} (hB : Opens.IsBasis B) :
    BasisSubgroups A where
  basis := B
  isBasis := hB
  subgroup := fun _ _ ↦ ⊤
  compatible := by intros; trivial

/-- The assigned subgroup of the full family is the full pointwise product. -/
theorem top_subgroup (A : X → AddCommGrpCat.{u}) {B : Set (Opens X)}
    (hB : Opens.IsBasis B) {U : Opens X} (hU : U ∈ B) :
    (top A hB).subgroup U hU = ⊤ := rfl

/-- A tuple is locally admissible if each point has a basis neighborhood on which its
restriction belongs to the assigned subgroup. -/
def locallyMem {A : X → AddCommGrpCat.{u}} (S : BasisSubgroups A) (U : Opens X)
    (s : ∀ x : U, A x) : Prop :=
  ∀ x : U, ∃ (V : Opens X) (hV : V ∈ S.basis) (hx : x.1 ∈ V) (hVU : V ≤ U),
    Set.restrict₂ (π := fun x ↦ A x) hVU s ∈ S.subgroup V hV

/-- The zero tuple is locally admissible. -/
theorem locallyMem_zero {A : X → AddCommGrpCat.{u}} (S : BasisSubgroups A)
    (U : Opens X) : S.locallyMem U 0 := sorry

/-- The sum of two locally admissible tuples is locally admissible. -/
theorem locallyMem_add {A : X → AddCommGrpCat.{u}} (S : BasisSubgroups A)
    (U : Opens X) {s t : ∀ x : U, A x}
    (hs : S.locallyMem U s) (ht : S.locallyMem U t) : S.locallyMem U (s + t) := sorry

/-- The negative of a locally admissible tuple is locally admissible. -/
theorem locallyMem_neg {A : X → AddCommGrpCat.{u}} (S : BasisSubgroups A)
    (U : Opens X) {s : ∀ x : U, A x} (hs : S.locallyMem U s) :
    S.locallyMem U (-s) := sorry

/-- The subgroup of tuples that locally belong to the assigned basis subgroups. -/
def sectionSubgroup {A : X → AddCommGrpCat.{u}} (S : BasisSubgroups A) (U : Opens X) :
    AddSubgroup (∀ x : U, A x) where
  carrier := {s | S.locallyMem U s}
  zero_mem' := S.locallyMem_zero U
  add_mem' := S.locallyMem_add U
  neg_mem' := S.locallyMem_neg U

/-- Membership in the local-sections subgroup is the basis-neighborhood condition. -/
theorem mem_sectionSubgroup {A : X → AddCommGrpCat.{u}} (S : BasisSubgroups A)
    (U : Opens X) (s : ∀ x : U, A x) :
    s ∈ S.sectionSubgroup U ↔
      ∀ x : U, ∃ (V : Opens X) (hV : V ∈ S.basis) (hx : x.1 ∈ V) (hVU : V ≤ U),
        Set.restrict₂ (π := fun x ↦ A x) hVU s ∈ S.subgroup V hV := Iff.rfl

/-- On a basis open, the assigned subgroup is contained in the local-sections subgroup. -/
theorem subgroup_le_sectionSubgroup {A : X → AddCommGrpCat.{u}} (S : BasisSubgroups A)
    {U : Opens X} (hU : U ∈ S.basis) :
    S.subgroup U hU ≤ S.sectionSubgroup U := sorry

/-- Restriction of a local section along an inclusion of opens is a local section. -/
theorem restrict_mem {A : X → AddCommGrpCat.{u}} (S : BasisSubgroups A)
    {U V : Opens X} (hUV : U ≤ V) {s : ∀ x : V, A x} (hs : s ∈ S.sectionSubgroup V) :
    Set.restrict₂ (π := fun x ↦ A x) hUV s ∈ S.sectionSubgroup U := sorry

/-- The abelian-group-valued presheaf of locally admissible tuples, with restriction maps. -/
def presheaf {A : X → AddCommGrpCat.{u}} (S : BasisSubgroups A) :
    X.Presheaf AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (S.sectionSubgroup U.unop)
  map i := AddCommGrpCat.ofHom
    { toFun := fun s ↦ ⟨Set.restrict₂ (π := fun x ↦ A x) i.unop.le s, S.restrict_mem i.unop.le s.property⟩
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- Objects of the local-sections presheaf are the local-sections subgroups. -/
theorem presheaf_obj {A : X → AddCommGrpCat.{u}} (S : BasisSubgroups A) (U : Opens X) :
    S.presheaf.obj (op U) = AddCommGrpCat.of (S.sectionSubgroup U) := rfl

/-- Locally admissible pointwise tuples form a sheaf of abelian groups. -/
@[stacks 0790]
theorem isSheaf {A : X → AddCommGrpCat.{u}} (S : BasisSubgroups A) :
    S.presheaf.IsSheaf := sorry

end BasisSubgroups

/-- The discrete two-point space. -/
abbrev finTwo : TopCat.{0} := TopCat.discrete.obj (Fin 2)

/-- Constant integer fibres on the discrete two-point space. -/
def finTwoConstantInt : finTwo → AddCommGrpCat.{0} :=
  fun _ ↦ AddCommGrpCat.of ℤ

/-- The subgroup is trivial on the whole two-point space and full on every proper open. -/
def finTwoSubgroup (U : Opens finTwo) : AddSubgroup (∀ x : U, finTwoConstantInt x) := by
  classical
  exact if U = ⊤ then ⊥ else ⊤

/-- Membership in the assigned subgroup requires the zero tuple precisely on the whole
space. -/
theorem mem_finTwoSubgroup (U : Opens finTwo) (s : ∀ x : U, finTwoConstantInt x) :
    s ∈ finTwoSubgroup U ↔ (U = ⊤ → s = 0) := by
  classical
  by_cases h : U = ⊤ <;> simp [finTwoSubgroup, h]

/-- The two-point subgroup family is stable under restriction. -/
theorem finTwoSubgroup_restrict_mem {U V : Opens finTwo} (hUV : U ≤ V)
    {s : ∀ x : V, finTwoConstantInt x} (hs : s ∈ finTwoSubgroup V) :
    Set.restrict₂ (π := fun x ↦ finTwoConstantInt x) hUV s ∈ finTwoSubgroup U := sorry

/-- The restriction-compatible subgroup family on the basis of all opens of the discrete
two-point space. -/
def finTwoBasisSubgroups : BasisSubgroups finTwoConstantInt where
  basis := Set.univ
  isBasis := Opens.isBasis_iff_nbhd.mpr (fun {U} {_} hx ↦
    ⟨U, Set.mem_univ U, hx, le_rfl⟩)
  subgroup := fun U _ ↦ finTwoSubgroup U
  compatible := fun _ _ hUV _ hs ↦ finTwoSubgroup_restrict_mem hUV hs

/-- On the whole discrete two-point space, the local-sections subgroup differs from the
assigned subgroup. -/
@[stacks 0790]
theorem finTwo_univ_ne :
    finTwoBasisSubgroups.sectionSubgroup ⊤ ≠
      finTwoBasisSubgroups.subgroup ⊤ (Set.mem_univ ⊤) := sorry

end TopCat.Presheaf.PointwiseProduct

end

end
