/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Action.SmallBoundClosed
public import Mathlib.SetTheory.ZFC.VonNeumann
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.Algebra.Group.TransferInstance

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Cardinal ZFSet

namespace Action

universe u

/-- A `G`-set on the small type of elements of an actual ZFC set. Native carriers
are not stored in this presentation, so arbitrary isomorphic copies are excluded. -/
structure SetPresentation (G : Type u) [Group G] where
  carrier : ZFSet.{u}
  ρ : G →* End (Shrink carrier)

namespace SetPresentation

variable {G : Type u} [Group G]

/-- Realization on the specified set, rather than on an arbitrary equivalent type. -/
def toAction (S : SetPresentation G) : Action (Type u) G :=
  ⟨Shrink S.carrier, S.ρ⟩

/-- The ZFC ordinal associated to mathlib's chosen well-order of a small type. -/
def typeSet (X : Type u) : ZFSet.{u} :=
  (Ordinal.type (@WellOrderingRel X)).toZFSet

/-- The maps are ordinal position and ordinal enumeration, followed by shrinking.
Their inverse laws use only proved mathlib results. -/
def typeSetEquiv (X : Type u) : X ≃ Shrink (typeSet X) :=
  (show X ≃ (typeSet X) from
    { toFun := fun x ↦ ⟨(Ordinal.typein (@WellOrderingRel X) x).toZFSet,
        Ordinal.toZFSet_mem_toZFSet_iff.2 (Ordinal.typein_lt_type _ x)⟩
      invFun := fun x ↦ Ordinal.enum (@WellOrderingRel X)
        ⟨x.val.rank, by
          obtain ⟨o, ho, he⟩ := Ordinal.mem_toZFSet_iff.1 x.property
          simpa [← he] using ho⟩
      left_inv := fun x ↦ by
        simp only [Ordinal.rank_toZFSet]
        exact Ordinal.enum_typein _ x
      right_inv := fun x ↦ by
        apply Subtype.ext
        change (Ordinal.typein (@WellOrderingRel X)
          (Ordinal.enum _ ⟨x.val.rank, _⟩)).toZFSet = x.val
        rw [Ordinal.typein_enum]
        obtain ⟨o, ho, he⟩ := Ordinal.mem_toZFSet_iff.1 x.property
        simp [← he] }).trans (equivShrink _)

/-- Transport the native group structure to its set carrier. This is deliberately
an explicit, non-global instance, since the chosen presentation is not definitional. -/
abbrev setGroup (G : Type u) [Group G] : Group (Shrink (typeSet G)) :=
  (typeSetEquiv G).symm.group

/-- The set-presented group and the native group have explicit inverse carrier maps. -/
def groupEquiv (G : Type u) [Group G] :
    letI := setGroup G
    Shrink (typeSet G) ≃* G :=
  (typeSetEquiv G).symm.mulEquiv

/-- Reuse restriction of actions along a group isomorphism to adapt an arbitrary
native acting group to the set-carrier convention in the source-facing theorem. -/
def actionEquivalence (G : Type u) [Group G] :
    letI := setGroup G
    Action (Type u) G ≌ Action (Type u) (Shrink (typeSet G)) :=
  letI := setGroup G
  Action.resEquiv (Type u) (groupEquiv G)

/-- A set label for a group element, with the group fixed throughout the encoding. -/
def groupVal (g : G) : ZFSet.{u} :=
  (Ordinal.typein (@WellOrderingRel G) g).toZFSet

omit [Group G] in
theorem groupVal_injective : Function.Injective (groupVal : G → ZFSet.{u}) :=
  Ordinal.toZFSet_injective.comp (Ordinal.typein_injective _)

/-- Read the set label of an element of the canonical carrier. -/
def val (S : SetPresentation G) (x : S.toAction.V) : ZFSet.{u} :=
  ((equivShrink S.carrier).symm x).val

theorem val_injective (S : SetPresentation G) : Function.Injective S.val :=
  Subtype.val_injective.comp (equivShrink S.carrier).symm.injective

/-- The graph of the action, with both input labels and the output label recorded. -/
def actionGraph (S : SetPresentation G) : ZFSet.{u} :=
  ZFSet.range (fun gx : G × S.toAction.V ↦
    ZFSet.pair (ZFSet.pair (groupVal gx.1) (S.val gx.2))
      (S.val (S.ρ gx.1 gx.2)))

/-- A complete code for an action of the fixed group: its carrier and action graph.
The group labels are injective ordinal positions, not arbitrary native type labels. -/
def code (S : SetPresentation G) : ZFSet.{u} :=
  ZFSet.pair S.carrier S.actionGraph

/-- A complete code determines the literal set presentation. -/
theorem code_injective : Function.Injective (code : SetPresentation G → ZFSet.{u}) := by
  intro S T h
  obtain ⟨hcarrier, hgraph⟩ := ZFSet.pair_inj.1 h
  cases S with
  | mk carrier ρS =>
    cases T with
    | mk carrierT ρT =>
      dsimp at hcarrier
      subst carrierT
      congr 1
      apply MonoidHom.ext
      intro g
      apply ConcreteCategory.ext_apply
      intro x
      have hx := ZFSet.mem_range_self
        (f := fun gx : G × Shrink carrier ↦
          ZFSet.pair (ZFSet.pair (groupVal gx.1)
            ((equivShrink carrier).symm gx.2).val)
            (((equivShrink carrier).symm (ρS gx.1 gx.2)).val)) (g, x)
      change _ ∈ actionGraph ⟨carrier, ρS⟩ at hx
      rw [hgraph] at hx
      obtain ⟨⟨other, y⟩, hy⟩ := ZFSet.mem_range.1 hx
      obtain ⟨hinput, houtput⟩ := ZFSet.pair_inj.1 hy
      obtain ⟨hgroup, hpoint⟩ := ZFSet.pair_inj.1 hinput
      have hg : other = g := groupVal_injective hgroup
      have hyx : y = x := (val_injective ⟨carrier, ρS⟩) hpoint
      subst other
      subst y
      exact ((val_injective ⟨carrier, ρS⟩) houtput).symm

/-- Transport an action along specified carrier maps. Only the action laws are proofs. -/
def transport (S : Action (Type u) G) {A : ZFSet.{u}}
    (e : S.V ≃ Shrink A) : SetPresentation G where
  carrier := A
  ρ :=
    { toFun := fun g ↦ ↾fun x ↦ e (S.ρ g (e.symm x))
      map_one' := by
        apply ConcreteCategory.ext_apply
        intro x
        change e (S.ρ 1 (e.symm x)) = x
        rw [map_one]
        exact e.apply_symm_apply x
      map_mul' := fun g h ↦ by
        apply ConcreteCategory.ext_apply
        intro x
        change e (S.ρ (g * h) (e.symm x)) =
          e (S.ρ g (e.symm (e (S.ρ h (e.symm x)))))
        rw [e.symm_apply_apply, map_mul]
        rfl }

/-- Both directions of the transport isomorphism are the supplied carrier maps. -/
def transportIso (S : Action (Type u) G) {A : ZFSet.{u}}
    (e : S.V ≃ Shrink A) : S ≅ (transport S e).toAction :=
  Action.mkIso e.toIso (fun g ↦ by
    apply ConcreteCategory.ext_apply
    intro x
    change e (S.ρ g x) = e (S.ρ g (e.symm (e x)))
    rw [e.symm_apply_apply])

/-- A canonical set representative of a native action; this changes its carrier. -/
def ofAction (S : Action (Type u) G) : SetPresentation G :=
  transport S (typeSetEquiv S.V)

/-- The canonical representative is isomorphic to the native action, not literally equal. -/
def ofActionIso (S : Action (Type u) G) : S ≅ (ofAction S).toAction :=
  transportIso S (typeSetEquiv S.V)

@[simp] theorem transport_ρ_apply (S : Action (Type u) G) {A : ZFSet.{u}}
    (e : S.V ≃ Shrink A) (g : G) (x : Shrink A) :
    (transport S e).ρ g x = e (S.ρ g (e.symm x)) := rfl

@[simp] theorem transportIso_hom_apply (S : Action (Type u) G) {A : ZFSet.{u}}
    (e : S.V ≃ Shrink A) (x : S.V) : (transportIso S e).hom.hom x = e x := rfl

@[simp] theorem transportIso_inv_apply (S : Action (Type u) G) {A : ZFSet.{u}}
    (e : S.V ≃ Shrink A) (x : Shrink A) :
    (transportIso S e).inv.hom x = e.symm x := rfl

/-- When the group already has a set carrier, its regular action is literally presented. -/
def leftRegular (A : ZFSet.{u}) [Group (Shrink A)] : SetPresentation (Shrink A) :=
  ⟨A, (Action.leftRegular (Shrink A)).ρ⟩

@[simp] theorem leftRegular_toAction (A : ZFSet.{u}) [Group (Shrink A)] :
    (leftRegular A).toAction = Action.leftRegular (Shrink A) := rfl

end SetPresentation

variable {G : Type u} [Group G]

/-- The literal representative stage `G-Sets_α`. Its objects have canonical set carriers;
its isomorphism closure is a separate object property and is not asserted small. -/
def vonNeumannStage (α : Ordinal.{u}) : ObjectProperty (Action (Type u) G) :=
  fun S ↦ ∃ T : SetPresentation G, T.toAction = S ∧ T.code ∈ V_ α

theorem mem_vonNeumannStage_iff (α : Ordinal.{u}) (S : Action (Type u) G) :
    vonNeumannStage α S ↔
      ∃ T : SetPresentation G, T.toAction = S ∧ T.code ∈ V_ α := Iff.rfl

theorem mem_vonNeumannStage (α : Ordinal.{u}) (S : SetPresentation G)
    (h : S.code ∈ V_ α) : vonNeumannStage α S.toAction := ⟨S, rfl, h⟩

/-- The actual stage is small, using the injective complete code, rather than smallness
of all native isomorphic copies. -/
theorem small_vonNeumannStage (α : Ordinal.{u}) :
    ObjectProperty.Small.{u} (vonNeumannStage α : ObjectProperty (Action (Type u) G)) := by
  have : Small.{u} { S : SetPresentation G // S.code ∈ V_ α } :=
    small_of_injective (f := fun S ↦ (⟨S.val.code, S.property⟩ : V_ α)) (by
      intro S T h
      apply Subtype.ext
      exact SetPresentation.code_injective (congrArg Subtype.val h))
  apply small_of_surjective
    (f := fun S : { S : SetPresentation G // S.code ∈ V_ α } ↦
      (⟨S.val.toAction, S.val, rfl, S.property⟩ : Subtype (vonNeumannStage α)))
  rintro ⟨S, T, hT, hcode⟩
  exact ⟨⟨T, hcode⟩, Subtype.ext hT⟩

/-- Native adaptation is through isomorphisms, whereas literal membership uses equality. -/
theorem isoClosure_vonNeumannStage_iff (α : Ordinal.{u}) (S : Action (Type u) G) :
    (vonNeumannStage α).isoClosure S ↔
      ∃ T : SetPresentation G, T.code ∈ V_ α ∧ Nonempty (S ≅ T.toAction) := by
  constructor
  · rintro ⟨T, ⟨U, rfl, hU⟩, ⟨e⟩⟩
    exact ⟨U, hU, ⟨e⟩⟩
  · rintro ⟨T, hT, ⟨e⟩⟩
    exact ⟨T.toAction, ⟨T, rfl, hT⟩, ⟨e⟩⟩

/-- An explicit common stage: the supremum of the required ranks plus `ω₁`.
Its uncountable cofinality bounds countably many earlier ranks and their finite
set-theoretic constructions. The extra presentation can be the regular action. -/
def vonNeumannStageOrdinal {ι : Type u} (S0 : ι → SetPresentation G)
    (L : SetPresentation G) : Ordinal.{u} :=
  ((SetPresentation.typeSet G).rank ⊔ L.code.rank ⊔
    (⨆ i, (S0 i).code.rank)) + (Cardinal.aleph 1).ord

theorem vonNeumannStageOrdinal_isSuccLimit {ι : Type u} (S0 : ι → SetPresentation G)
    (L : SetPresentation G) : Order.IsSuccLimit (vonNeumannStageOrdinal S0 L) :=
  Ordinal.isSuccLimit_add _ (Cardinal.isSuccLimit_ord (Cardinal.aleph0_le_aleph _))

/-- The common stage has cofinality `ℵ₁`; taking only a countable limit of ranks
would not suffice for countable diagrams. -/
theorem vonNeumannStageOrdinal_cof {ι : Type u} (S0 : ι → SetPresentation G)
    (L : SetPresentation G) : (vonNeumannStageOrdinal S0 L).cof = Cardinal.aleph 1 := by
  unfold vonNeumannStageOrdinal
  rw [Ordinal.cof_add _ (ne_of_gt (Cardinal.ord_pos.2 (Cardinal.aleph_pos 1)))]
  simpa using (Cardinal.isRegular_aleph_add_one 0).cof_ord

theorem mem_vonNeumannStageOrdinal {ι : Type u} (S0 : ι → SetPresentation G)
    (L : SetPresentation G) (i : ι) :
    (S0 i).code ∈ V_ (vonNeumannStageOrdinal S0 L) := by
  rw [ZFSet.mem_vonNeumann]
  exact lt_of_le_of_lt ((le_ciSup Ordinal.bddAbove_of_small i).trans le_sup_right)
    (lt_add_of_pos_right _ (Cardinal.ord_pos.2 (Cardinal.aleph_pos 1)))

theorem extra_mem_vonNeumannStageOrdinal {ι : Type u} (S0 : ι → SetPresentation G)
    (L : SetPresentation G) : L.code ∈ V_ (vonNeumannStageOrdinal S0 L) := by
  rw [ZFSet.mem_vonNeumann]
  exact lt_of_le_of_lt (le_sup_of_le_left le_sup_right)
    (lt_add_of_pos_right _ (Cardinal.ord_pos.2 (Cardinal.aleph_pos 1)))

/-- The bound comparison supplies a representative in the literal stage. -/
theorem vonNeumannStage_isoClosure_of_size_le_bound {ι : Type u}
    (S0 : ι → SetPresentation G) (L : SetPresentation G)
    {S T : Action (Type u) G} (hS : vonNeumannStage (vonNeumannStageOrdinal S0 L) S)
    (hT : T.size ≤ bound S.size) :
    (vonNeumannStage (vonNeumannStageOrdinal S0 L)).isoClosure T := sorry

theorem vonNeumannStage_hasLimit {ι : Type u} (S0 : ι → SetPresentation G)
    (L : SetPresentation G) {J : Type} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ (vonNeumannStage (G := G) (vonNeumannStageOrdinal S0 L)).FullSubcategory) :
    HasLimit F := sorry

theorem vonNeumannStage_isIso_limit_post {ι : Type u} (S0 : ι → SetPresentation G)
    (L : SetPresentation G) {J : Type} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ (vonNeumannStage (G := G) (vonNeumannStageOrdinal S0 L)).FullSubcategory)
    [HasLimit F] [HasLimit (F ⋙ (vonNeumannStage (G := G) (vonNeumannStageOrdinal S0 L)).ι)] :
    IsIso (limit.post F (vonNeumannStage (G := G) (vonNeumannStageOrdinal S0 L)).ι) := sorry

theorem vonNeumannStage_hasColimit {ι : Type u} (S0 : ι → SetPresentation G)
    (L : SetPresentation G) {J : Type} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ (vonNeumannStage (G := G) (vonNeumannStageOrdinal S0 L)).FullSubcategory) :
    HasColimit F := sorry

theorem vonNeumannStage_isIso_colimit_post {ι : Type u} (S0 : ι → SetPresentation G)
    (L : SetPresentation G) {J : Type} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ (vonNeumannStage (G := G) (vonNeumannStageOrdinal S0 L)).FullSubcategory)
    [HasColimit F] [HasColimit (F ⋙ (vonNeumannStage (G := G) (vonNeumannStageOrdinal S0 L)).ι)] :
    IsIso (colimit.post F (vonNeumannStage (G := G) (vonNeumannStageOrdinal S0 L)).ι) := sorry

/-- The abstract owner applies to the actual stage when the regular action is literally
set-presented. This condition is realized by `SetPresentation.leftRegular`. -/
theorem vonNeumannStage_isSmallBoundClosed {ι : Type u} (S0 : ι → SetPresentation G)
    (L : SetPresentation G) (hL : L.toAction = Action.leftRegular G) :
    IsSmallBoundClosed (vonNeumannStage (G := G) (vonNeumannStageOrdinal S0 L)) where
  small := small_vonNeumannStage _
  contains_leftRegular := hL ▸ mem_vonNeumannStage _ L
    (extra_mem_vonNeumannStageOrdinal S0 L)
  isoClosure_of_size_le_bound := vonNeumannStage_isoClosure_of_size_le_bound S0 L
  hasLimit := vonNeumannStage_hasLimit S0 L
  isIso_limit_post := vonNeumannStage_isIso_limit_post S0 L
  hasColimit := vonNeumannStage_hasColimit S0 L
  isIso_colimit_post := vonNeumannStage_isIso_colimit_post S0 L

/-- Source-facing 000U: for a group on a set carrier and a family on set carriers,
the explicit common limit stage satisfies the old abstract API, usable also by 000V. -/
theorem exists_vonNeumannStage (A : ZFSet.{u}) [Group (Shrink A)] {ι : Type u}
    (S0 : ι → SetPresentation (Shrink A)) :
    ∃ α : Ordinal.{u}, Order.IsSuccLimit α ∧
      IsSmallBoundClosed (vonNeumannStage α : ObjectProperty (Action (Type u) (Shrink A))) ∧
      ∀ i, vonNeumannStage α (S0 i).toAction := by
  let L := SetPresentation.leftRegular A
  exact ⟨vonNeumannStageOrdinal S0 L, vonNeumannStageOrdinal_isSuccLimit S0 L,
    vonNeumannStage_isSmallBoundClosed S0 L rfl,
    fun i ↦ mem_vonNeumannStage _ _ (mem_vonNeumannStageOrdinal S0 L i)⟩

/-- For an arbitrary native family the canonical representatives lie in one explicit
stage. The conclusions about the original family and regular action are isomorphisms. -/
theorem nativeFamily_mem_isoClosure_vonNeumannStage {ι : Type u}
    (S0 : ι → Action (Type u) G) :
    let α := vonNeumannStageOrdinal (fun i ↦ SetPresentation.ofAction (S0 i))
      (SetPresentation.ofAction (Action.leftRegular G))
    (∀ i, (vonNeumannStage α).isoClosure (S0 i)) ∧
      (vonNeumannStage α).isoClosure (Action.leftRegular G) := by
  constructor
  · intro i
    apply (isoClosure_vonNeumannStage_iff _ _).2
    exact ⟨SetPresentation.ofAction (S0 i), mem_vonNeumannStageOrdinal _ _ i,
      ⟨SetPresentation.ofActionIso (S0 i)⟩⟩
  · apply (isoClosure_vonNeumannStage_iff _ _).2
    exact ⟨SetPresentation.ofAction (Action.leftRegular G),
      extra_mem_vonNeumannStageOrdinal _ _, ⟨SetPresentation.ofActionIso _⟩⟩

end Action
