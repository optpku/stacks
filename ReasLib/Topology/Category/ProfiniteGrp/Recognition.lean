module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
public import ReasLib.Topology.Algebra.OpenNormalSubgroup
public import ReasLib.Topology.Category.Profinite.Recognition

/-!
# Recognition of profinite topological groups

The bundled category `ProfiniteGrp` is the canonical owner.  This module gives unbundled
recognition and finite-discrete-limit presentations without introducing a parallel predicate for
profinite groups.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ProfiniteGrp

/-- A presentation of a topological group as a limit of finite groups equipped with their discrete
profinite topologies. -/
@[stacks 0BR1 "finite discrete limit presentation"]
structure FiniteLimitPresentation (G : Type u) [Group G] [TopologicalSpace G] where
  /-- The small indexing category. -/
  index : Type u
  /-- The category structure on the index. -/
  instSmallCategory : SmallCategory index
  /-- The finite-group diagram. -/
  diagram : index ⥤ FiniteGrp.{u}
  /-- The chosen continuous group isomorphism from the presented group to the limit. -/
  continuousMulEquiv :
    G ≃ₜ* ProfiniteGrp.limit (diagram ⋙ forget₂ FiniteGrp ProfiniteGrp)

attribute [instance] FiniteLimitPresentation.instSmallCategory

namespace FiniteLimitPresentation

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Build a finite-limit presentation from a small finite-group diagram and its chosen limit
comparison. -/
def ofContinuousMulEquiv {J : Type u} [SmallCategory J] (diagram : J ⥤ FiniteGrp.{u})
    (continuousMulEquiv :
      G ≃ₜ* ProfiniteGrp.limit (diagram ⋙ forget₂ FiniteGrp ProfiniteGrp)) :
    FiniteLimitPresentation G where
  index := J
  instSmallCategory := inferInstance
  diagram := diagram
  continuousMulEquiv := continuousMulEquiv

end FiniteLimitPresentation

/-- A cofiltered finite-limit presentation of a topological group. -/
@[stacks 0BR1 "cofiltered finite discrete limit presentation"]
structure CofilteredFiniteLimitPresentation (G : Type u) [Group G] [TopologicalSpace G]
    extends FiniteLimitPresentation G where
  /-- Cofilteredness of the indexing category. -/
  instIsCofiltered : IsCofiltered index

attribute [instance] CofilteredFiniteLimitPresentation.instIsCofiltered

namespace CofilteredFiniteLimitPresentation

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Build a cofiltered finite-limit presentation from a cofiltered finite-group diagram and its
chosen limit comparison. -/
def ofContinuousMulEquiv {J : Type u} [SmallCategory J] [IsCofiltered J]
    (diagram : J ⥤ FiniteGrp.{u})
    (continuousMulEquiv :
      G ≃ₜ* ProfiniteGrp.limit (diagram ⋙ forget₂ FiniteGrp ProfiniteGrp)) :
    CofilteredFiniteLimitPresentation G where
  toFiniteLimitPresentation :=
    { index := J
      instSmallCategory := inferInstance
      diagram := diagram
      continuousMulEquiv := continuousMulEquiv }
  instIsCofiltered := inferInstance

/-- The canonical cofiltered finite-quotient presentation of a bundled profinite group. -/
noncomputable def ofProfiniteGrp (P : ProfiniteGrp.{u}) :
    CofilteredFiniteLimitPresentation P :=
  ofContinuousMulEquiv P.toFiniteQuotientFunctor
    P.continuousMulEquivLimittoFiniteQuotientFunctor

/-- The canonical cofiltered finite-quotient presentation of a compact totally disconnected
topological group. This exposes Mathlib's bundled `ProfiniteGrp.of G` construction as concrete
presentation data, so a downstream limit argument need not choose a witness from a recognition
theorem. -/
@[stacks 0BR1 "cofiltered finite presentation of a compact totally disconnected group"]
noncomputable def ofCompactTotallyDisconnected
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] :
    CofilteredFiniteLimitPresentation G :=
  ofProfiniteGrp (ProfiniteGrp.of G)

end CofilteredFiniteLimitPresentation

/-- `G` admits a presentation as a limit of finite groups equipped with their discrete profinite
topologies. -/
@[stacks 0BR1 "finite discrete limit presentation"]
def HasFiniteLimitPresentation (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  Nonempty (FiniteLimitPresentation G)

/-- `G` admits a finite discrete limit presentation indexed by a cofiltered category. -/
@[stacks 0BR1 "cofiltered finite discrete limit presentation"]
def HasCofilteredFiniteLimitPresentation (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  Nonempty (CofilteredFiniteLimitPresentation G)

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- An unbundled topological group has a profinite-space model exactly when it has a bundled
profinite-group model. -/
@[stacks 0BR1 "profinite spaces and bundled profinite groups"]
theorem exists_homeomorph_iff_exists_continuousMulEquiv :
    (∃ P : Profinite.{u}, Nonempty (G ≃ₜ P)) ↔
      ∃ P : ProfiniteGrp.{u}, Nonempty (G ≃ₜ* P) := sorry

/-- An unbundled topological group has a bundled profinite-group model exactly when it is compact
and totally disconnected. -/
@[stacks 0BR1 "compact totally disconnected recognition of profinite groups"]
theorem exists_continuousMulEquiv_iff_compact_totallyDisconnected :
    (∃ P : ProfiniteGrp.{u}, Nonempty (G ≃ₜ* P)) ↔
      CompactSpace G ∧ TotallyDisconnectedSpace G := sorry

/-- A topological group has a finite discrete limit presentation exactly when it is compact and
totally disconnected. -/
@[stacks 0BR1 "finite discrete limit recognition of profinite groups"]
theorem hasFiniteLimitPresentation_iff_compact_totallyDisconnected :
    HasFiniteLimitPresentation G ↔ CompactSpace G ∧ TotallyDisconnectedSpace G := sorry

/-- A topological group has a cofiltered finite discrete limit presentation exactly when it is
compact and totally disconnected. -/
@[stacks 0BR1 "cofiltered finite discrete limit recognition of profinite groups"]
theorem hasCofilteredFiniteLimitPresentation_iff_compact_totallyDisconnected :
    HasCofilteredFiniteLimitPresentation G ↔ CompactSpace G ∧ TotallyDisconnectedSpace G := sorry

/-- Lemma 5.30.4: a topological group is profinite exactly when it admits a finite discrete group
limit presentation, equivalently one indexed by a cofiltered category. -/
@[stacks 0BR1 "finite discrete limit presentations of profinite groups"]
theorem profinite_tfae :
    List.TFAE
      [ ∃ P : Profinite.{u}, Nonempty (G ≃ₜ P),
        HasFiniteLimitPresentation G,
        HasCofilteredFiniteLimitPresentation G ] := sorry

end ProfiniteGrp
