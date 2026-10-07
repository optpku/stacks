module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.Sheaves.Pointwise.Product.Algebraic

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace TopCat.Presheaf.PointwiseProduct

variable {X : TopCat.{u}}

/-- Restriction of a pointwise tuple along an inclusion of opens. -/
def restrict {A : X → AddCommGrpCat.{u}} {U V : Opens X} (hUV : U ≤ V)
    (s : ∀ x : V, A x) (x : U) : A x :=
  s (Opens.inclusion hUV x)

/-- Restriction of a pointwise tuple is precomposition with `Opens.inclusion`. -/
theorem restrict_apply {A : X → AddCommGrpCat.{u}} {U V : Opens X} (hUV : U ≤ V)
    (s : ∀ x : V, A x) (x : U) :
    restrict hUV s x = s (Opens.inclusion hUV x) := sorry

/-- A restriction-compatible family of subgroups of the pointwise product on a topological
basis. -/
structure BasisSubgroups {X : TopCat.{u}} (A : X → AddCommGrpCat.{u}) where
  basis : Set (Opens X)
  isBasis : Opens.IsBasis basis
  subgroup : ∀ U, U ∈ basis → AddSubgroup (∀ x : U, A x)
  compatible : ∀ {U V} (hU : U ∈ basis) (hV : V ∈ basis) (hUV : U ≤ V)
      {s : ∀ x : V, A x}, s ∈ subgroup V hV → restrict hUV s ∈ subgroup U hU

namespace BasisSubgroups

/-- The family of full pointwise product groups on a basis. -/
def top (A : X → AddCommGrpCat.{u}) {B : Set (Opens X)} (hB : Opens.IsBasis B) :
    BasisSubgroups A where
  basis := B
  isBasis := hB
  subgroup := fun _ _ ↦ ⊤
  compatible := sorry

/-- The assigned subgroup of `top A hB` on a basis open is the full pointwise product. -/
theorem top_subgroup (A : X → AddCommGrpCat.{u}) {B : Set (Opens X)}
    (hB : Opens.IsBasis B) {U : Opens X} (hU : U ∈ B) :
    (top A hB).subgroup U hU = ⊤ := sorry

/-- The local-sections subgroup `F(U)`: tuples that, near every point, restrict into the
given subgroup on some basis neighborhood. -/
def sectionSubgroup {A : X → AddCommGrpCat.{u}} (S : BasisSubgroups A) (U : Opens X) :
    AddSubgroup (∀ x : U, A x) where
  carrier := {s | ∀ x : U,
    ∃ (V : Opens X) (hV : V ∈ S.basis) (hx : x.1 ∈ V) (hVU : V ≤ U),
      restrict hVU s ∈ S.subgroup V hV}
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry

/-- Membership in `sectionSubgroup` is the source local-neighborhood condition. -/
theorem mem_sectionSubgroup {A : X → AddCommGrpCat.{u}} (S : BasisSubgroups A)
    (U : Opens X) (s : ∀ x : U, A x) :
    s ∈ S.sectionSubgroup U ↔
      ∀ x : U, ∃ (V : Opens X) (hV : V ∈ S.basis) (hx : x.1 ∈ V) (hVU : V ≤ U),
        restrict hVU s ∈ S.subgroup V hV := sorry

/-- On a basis open, the given subgroup is contained in the local-sections subgroup. -/
theorem subgroup_le_sectionSubgroup {A : X → AddCommGrpCat.{u}} (S : BasisSubgroups A)
    {U : Opens X} (hU : U ∈ S.basis) :
    S.subgroup U hU ≤ S.sectionSubgroup U := sorry

/-- Restriction of a local section along an inclusion of opens is again a local section. -/
theorem restrict_mem {A : X → AddCommGrpCat.{u}} (S : BasisSubgroups A)
    {U V : Opens X} (hUV : U ≤ V) {s : ∀ x : V, A x} (hs : s ∈ S.sectionSubgroup V) :
    restrict hUV s ∈ S.sectionSubgroup U := sorry

/-- The abelian-group-valued presheaf with sections `sectionSubgroup`. -/
def presheaf {A : X → AddCommGrpCat.{u}} (S : BasisSubgroups A) :
    X.Presheaf AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (S.sectionSubgroup U.unop)
  map i := AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (fun s ↦ ⟨restrict i.unop.le s, sorry⟩) sorry)
  map_id := sorry
  map_comp := sorry

/-- Objects of the local-sections presheaf are the local-sections subgroups. -/
theorem presheaf_obj {A : X → AddCommGrpCat.{u}} (S : BasisSubgroups A) (U : Opens X) :
    S.presheaf.obj (op U) = AddCommGrpCat.of (S.sectionSubgroup U) := sorry

/-- Exercise 111.32.10 (1): if `S` is a restriction-compatible family of subgroups of the
pointwise product sheaf `presheaf A` from Exercise 111.32.9, on a basis for the topology of
`X` (Topology, Definition 5.5.1, packaged as `Opens.IsBasis`), then the local-sections
assignment `S.presheaf` is a sheaf of abelian groups. -/
@[stacks 0790]
theorem isSheaf {A : X → AddCommGrpCat.{u}} (S : BasisSubgroups A) :
    S.presheaf.IsSheaf := sorry

end BasisSubgroups

/-- The discrete two-point space. -/
abbrev finTwo : TopCat.{0} := TopCat.of (Fin 2)

/-- Constant integer fibres on the discrete two-point space. -/
def finTwoConstantInt : finTwo → AddCommGrpCat.{0} :=
  fun _ ↦ AddCommGrpCat.of ℤ

/-- The example subgroups: trivial on the whole space, and full on every proper open. -/
def finTwoSubgroup (U : Opens finTwo) : AddSubgroup (∀ x : U, finTwoConstantInt x) where
  carrier := {s | U = ⊤ → s = 0}
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry

/-- Membership in `finTwoSubgroup` is triviality of the tuple when the open is the whole
space. -/
theorem mem_finTwoSubgroup (U : Opens finTwo) (s : ∀ x : U, finTwoConstantInt x) :
    s ∈ finTwoSubgroup U ↔ (U = ⊤ → s = 0) := sorry

/-- The restriction-compatible family on all opens of the discrete two-point space. -/
def finTwoBasisSubgroups : BasisSubgroups finTwoConstantInt where
  basis := Set.univ
  isBasis := sorry
  subgroup := fun U _ ↦ finTwoSubgroup U
  compatible := sorry

/-- Exercise 111.32.10 (2): on the discrete two-point space with constant integer fibres,
trivial subgroup on the whole space and full subgroups on proper basis opens, the
local-sections group on `⊤` is not equal to the given subgroup on `⊤`. -/
@[stacks 0790]
theorem finTwo_univ_ne :
    finTwoBasisSubgroups.sectionSubgroup ⊤ ≠
      finTwoBasisSubgroups.subgroup ⊤ (Set.mem_univ ⊤) := sorry

end TopCat.Presheaf.PointwiseProduct

end

end
