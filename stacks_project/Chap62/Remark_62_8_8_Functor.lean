/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import ReasLib.AlgebraicGeometry.CycleGroup
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.WeakNormalization.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.LocallyNoetherian
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.Functor
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.Scheme.Seminormal
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Presentation
public import ReasLib.CategoryTheory.Sites.Sheafification.Map
public import stacks_project.Chap62.Definition_62_6_1_Specialization
public import stacks_project.Chap62.Definition_62_8_1_Effective
public import stacks_project.Chap62.Lemma_62_6_14
public import stacks_project.Chap62.Lemma_62_6_16
public import stacks_project.Chap62.Lemma_62_8_2

/-!
# The effective relative-cycle functor on locally finite type slices

This file names the contravariant functor sending an `S`-scheme locally of
finite type to the monoid `z^{eff}(X'/S', r)` of effective relative `r`-cycles
on the base change of `f : X ⟶ S`, together with its seminormal and weakly
normal restrictions and the comparison with reductions.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Schemes locally of finite type over a fixed base `S`. -/
abbrev LocallyOfFiniteTypeOver (S : Scheme.{u}) :=
  MorphismProperty.Over (@LocallyOfFiniteType) ⊤ S

/-- The structure morphism of an object of `LocallyOfFiniteTypeOver S` is
locally of finite type. -/
instance instLocallyOfFiniteType_hom {S : Scheme.{u}} (X : LocallyOfFiniteTypeOver S) :
    LocallyOfFiniteType X.hom :=
  X.prop

/-- A scheme locally of finite type over a locally Noetherian scheme is locally
Noetherian. -/
instance instIsLocallyNoetherian_left {S : Scheme.{u}} [IsLocallyNoetherian S]
    (X : LocallyOfFiniteTypeOver S) : IsLocallyNoetherian X.left :=
  sorry

/-- Unfolding `Functor.id` on the domain of a locally finite type `S`-scheme. -/
instance instIsLocallyNoetherian_id_left {S : Scheme.{u}} [IsLocallyNoetherian S]
    (X : LocallyOfFiniteTypeOver S) : IsLocallyNoetherian ((𝟭 Scheme).obj X.left) :=
  instIsLocallyNoetherian_left X

/-- The generic-point coproduct of a locally finite type `S`-scheme is
quasi-compact. -/
instance instQuasiCompact_genericPoints {S : Scheme.{u}} [IsLocallyNoetherian S]
    (X : LocallyOfFiniteTypeOver S) :
    QuasiCompact (genericPointSpectrumCoproductTo X.left) :=
  Scheme.Normalization.LocallyNoetherian.instGenericPointsQuasiCompact X.left

/-- The generic-point coproduct of a locally finite type `S`-scheme is
quasi-separated. -/
instance instQuasiSeparated_genericPoints {S : Scheme.{u}} [IsLocallyNoetherian S]
    (X : LocallyOfFiniteTypeOver S) :
    QuasiSeparated (genericPointSpectrumCoproductTo X.left) :=
  Scheme.Normalization.LocallyNoetherian.instGenericPointsQuasiSeparated X.left

/-- Seminormal objects of `LocallyOfFiniteTypeOver S`. -/
abbrev SeminormalOver (S : Scheme.{u}) :=
  ObjectProperty.FullSubcategory fun (X : LocallyOfFiniteTypeOver S) =>
    Scheme.Seminormal X.left

/-- The forgetful functor from seminormal locally finite type `S`-schemes. -/
abbrev SeminormalOver.ι (S : Scheme.{u}) :
    SeminormalOver S ⥤ LocallyOfFiniteTypeOver S :=
  ObjectProperty.ι fun (X : LocallyOfFiniteTypeOver S) => Scheme.Seminormal X.left

/-- Weakly normal objects of `LocallyOfFiniteTypeOver S`. -/
abbrev WeaklyNormalOver (S : Scheme.{u}) [IsLocallyNoetherian S] :=
  ObjectProperty.FullSubcategory fun (X : LocallyOfFiniteTypeOver S) =>
    Scheme.WeaklyNormal X.left

/-- The forgetful functor from weakly normal locally finite type `S`-schemes. -/
abbrev WeaklyNormalOver.ι (S : Scheme.{u}) [IsLocallyNoetherian S] :
    WeaklyNormalOver S ⥤ LocallyOfFiniteTypeOver S :=
  ObjectProperty.ι fun (X : LocallyOfFiniteTypeOver S) => Scheme.WeaklyNormal X.left

/-- Morphisms in `LocallyOfFiniteTypeOver S` are locally of finite type. -/
instance instLocallyOfFiniteType_overHom {S : Scheme.{u}}
    {X Y : LocallyOfFiniteTypeOver S} (φ : X ⟶ Y) :
    LocallyOfFiniteType φ.left :=
  sorry

/-- Nested pullback projections of a locally finite type morphism remain locally
of finite type. -/
instance instLocallyOfFiniteType_nestedPullbackSnd {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {S' S'' : LocallyOfFiniteTypeOver S} (φ : S'' ⟶ S') :
    LocallyOfFiniteType (pullback.snd (pullback.snd f S'.hom) φ.left) :=
  sorry

/-- Base change of an effective relative `r`-cycle remains effective. -/
theorem effectiveBaseChange_mem {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsLocallyNoetherian S] [IsLocallyNoetherian S'] [LocallyOfFiniteType f]
    (r : ℕ) (α : effective f r) :
    baseChange f g r (α : Family f r) ∈ effective (pullback.snd f g) r :=
  sorry

/-- Base change of effective relative `r`-cycles along `g : S' ⟶ S`. -/
def effectiveBaseChange {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsLocallyNoetherian S] [IsLocallyNoetherian S'] [LocallyOfFiniteType f]
    (r : ℕ) : effective f r →+ effective (pullback.snd f g) r :=
  ((baseChange f g r).restrict (effective f r)).codRestrict
    (effective (pullback.snd f g) r) (effectiveBaseChange_mem f g r)

/-- The underlying fibrewise family of `effectiveBaseChange` is family-level
base change. -/
theorem effectiveBaseChange_apply {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsLocallyNoetherian S] [IsLocallyNoetherian S'] [LocallyOfFiniteType f]
    (r : ℕ) (α : effective f r) :
    (effectiveBaseChange f g r α : Family (pullback.snd f g) r) =
      baseChange f g r (α : Family f r) :=
  sorry

/-- Membership of a base-changed effective cycle in `z^{eff}(X'/S', r)`. -/
theorem mem_effectiveBaseChange {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsLocallyNoetherian S] [IsLocallyNoetherian S'] [LocallyOfFiniteType f]
    (r : ℕ) (α : effective f r) :
    (effectiveBaseChange f g r α : Family (pullback.snd f g) r) ∈
      effective (pullback.snd f g) r :=
  sorry

/-- The fibre map induced by an isomorphism of morphisms over a common base. -/
def fiberMapOfIsoOver {X X' S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S}
    (e : X ⟶ X') (w : e ≫ f' = f) (s : S) :
    f.fiber s ⟶ f'.fiber s :=
  Scheme.Hom.fiberMap f e (𝟙 S) f' ⟨sorry⟩ s

/-- An isomorphism of morphisms over a common base induces isomorphisms of
scheme-theoretic fibres. -/
instance instIsIso_fiberMapOfIsoOver {X X' S : Scheme.{u}} {f : X ⟶ S}
    {f' : X' ⟶ S} (e : X ⟶ X') [IsIso e] (w : e ≫ f' = f) (s : S) :
    IsIso (fiberMapOfIsoOver e w s) :=
  sorry

/-- Transport of fibrewise cycle families along an isomorphism of morphisms over
a common base. -/
def familyMapOfIsoOver {X X' S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S}
    (e : X ⟶ X') [IsIso e] (w : e ≫ f' = f) (r : ℕ) :
    Family f r →+ Family f' r where
  toFun α s :=
    CycleGroup.mapHom (fiberMapOfIsoOver e w s)
      (f.fiberDimensionFunction s) (f'.fiberDimensionFunction s) r (α s)
  map_zero' := sorry
  map_add' := sorry

/-- Evaluating `familyMapOfIsoOver` is pushforward of fibre cycles along the
induced fibre isomorphism. -/
theorem familyMapOfIsoOver_apply {X X' S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S}
    (e : X ⟶ X') [IsIso e] (w : e ≫ f' = f) (r : ℕ) (α : Family f r) (s : S) :
    familyMapOfIsoOver e w r α s =
      CycleGroup.mapHom (fiberMapOfIsoOver e w s)
        (f.fiberDimensionFunction s) (f'.fiberDimensionFunction s) r (α s) :=
  sorry

/-- Transport of effective relative cycles along an isomorphism of morphisms over
a common base remains effective. -/
theorem effectiveMapOfIsoOver_mem {X X' S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    (e : X ⟶ X') [IsIso e] (w : e ≫ f' = f) (r : ℕ) (α : effective f r) :
    familyMapOfIsoOver e w r (α : Family f r) ∈ effective f' r :=
  sorry

/-- Transport of effective relative cycles along an isomorphism of morphisms over
a common base. -/
def effectiveMapOfIsoOver {X X' S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    (e : X ⟶ X') [IsIso e] (w : e ≫ f' = f) (r : ℕ) :
    effective f r →+ effective f' r :=
  ((familyMapOfIsoOver e w r).restrict (effective f r)).codRestrict
    (effective f' r) (effectiveMapOfIsoOver_mem e w r)

/-- Transport of relative cycle groups along an isomorphism of morphisms over a
common base remains relative. -/
theorem groupMapOfIsoOver_mem {X X' S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    (e : X ⟶ X') [IsIso e] (w : e ≫ f' = f) (r : ℕ) (α : group f r) :
    familyMapOfIsoOver e w r (α : Family f r) ∈ group f' r :=
  sorry

/-- Transport of relative cycle groups along an isomorphism of morphisms over a
common base. -/
def groupMapOfIsoOver {X X' S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    (e : X ⟶ X') [IsIso e] (w : e ≫ f' = f) (r : ℕ) :
    group f r →+ group f' r :=
  ((familyMapOfIsoOver e w r).restrict (group f r)).codRestrict
    (group f' r) (groupMapOfIsoOver_mem e w r)

/-- The associator identifying a nested pullback of `f` with the pullback along
the composite structure map. -/
def pullbackSndAssocIso {X S S' S'' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (h : S'' ⟶ S') :
    pullback (pullback.snd f g) h ≅ pullback f (h ≫ g) :=
  pullbackLeftPullbackSndIso f g h

/-- The associator commutes with the projections to the varying base. -/
theorem pullbackSndAssocIso_hom_snd {X S S' S'' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) (h : S'' ⟶ S') :
    (pullbackSndAssocIso f g h).hom ≫ pullback.snd f (h ≫ g) =
      pullback.snd (pullback.snd f g) h :=
  sorry

/-- The associator for a morphism of locally finite type `S`-schemes is a
morphism over the source. -/
theorem effectiveFunctor_map_over {X S : Scheme.{u}} (f : X ⟶ S)
    {S' S'' : LocallyOfFiniteTypeOver S} (φ : S'' ⟶ S') :
    ((pullbackSndAssocIso f S'.hom φ.left ≪≫
          pullback.congrHom rfl (MorphismProperty.Over.w φ)).hom) ≫
        pullback.snd f S''.hom =
      pullback.snd (pullback.snd f S'.hom) φ.left :=
  sorry

/-- Base-change maps of the effective functor along a morphism of locally finite
type `S`-schemes. -/
def effectiveFunctor_map {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    {S' S'' : LocallyOfFiniteTypeOver S} (φ : S'' ⟶ S') :
    effective (pullback.snd f S'.hom) r →+
      effective (pullback.snd f S''.hom) r where
  toFun α :=
    ⟨familyMapOfIsoOver
        ((pullbackSndAssocIso f S'.hom φ.left ≪≫
            pullback.congrHom rfl (MorphismProperty.Over.w φ)).hom)
        (effectiveFunctor_map_over f φ) r
        (baseChange (pullback.snd f S'.hom) φ.left r (α : Family (pullback.snd f S'.hom) r)),
      sorry⟩
  map_zero' := sorry
  map_add' := sorry

/-- The contravariant functor `S' ↦ z^{eff}(S' ×_S X / S', r)` on schemes
locally of finite type over `S`. -/
def effectiveFunctor {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) :
    (LocallyOfFiniteTypeOver S)ᵒᵖ ⥤ Type u where
  obj S' := effective (pullback.snd f S'.unop.hom) r
  map φ := TypeCat.ofHom (effectiveFunctor_map f r φ.unop).toFun
  map_id := sorry
  map_comp := sorry

/-- Evaluating `effectiveFunctor` at `S'` recovers `z^{eff}(S' ×_S X / S', r)`. -/
theorem effectiveFunctor_obj {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    (S' : LocallyOfFiniteTypeOver S) :
    (effectiveFunctor f r).obj (op S') =
      effective (pullback.snd f S'.hom) r :=
  sorry

/-- The action of `effectiveFunctor` on a morphism of bases is
`effectiveFunctor_map`. -/
theorem effectiveFunctor_map_apply {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    {S' S'' : LocallyOfFiniteTypeOver S} (φ : S'' ⟶ S')
    (α : effective (pullback.snd f S'.hom) r) :
    (effectiveFunctor f r).map φ.op α = effectiveFunctor_map f r φ α :=
  sorry

/-- The restriction of `effectiveFunctor` to seminormal locally finite type
`S`-schemes. -/
def effectiveFunctorSeminormal {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) :
    (SeminormalOver S)ᵒᵖ ⥤ Type u :=
  (SeminormalOver.ι S).op ⋙ effectiveFunctor f r

/-- The restriction of `effectiveFunctor` to weakly normal locally finite type
`S`-schemes. -/
def effectiveFunctorWeaklyNormal {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) :
    (WeaklyNormalOver S)ᵒᵖ ⥤ Type u :=
  (WeaklyNormalOver.ι S).op ⋙ effectiveFunctor f r

/-- The comparison morphism from the reduction of `X` to the pullback of `f`
along the reduction inclusion of `S`. -/
def reductionComparison {X S : Scheme.{u}} (f : X ⟶ S) :
    Scheme.reduction X ⟶ pullback f (Scheme.reductionι S) :=
  pullback.lift (Scheme.reductionι X) (Scheme.reductionMap f) sorry

/-- The comparison morphism projects to the reduction of `f`. -/
theorem reductionComparison_snd {X S : Scheme.{u}} (f : X ⟶ S) :
    reductionComparison f ≫ pullback.snd f (Scheme.reductionι S) =
      Scheme.reductionMap f :=
  sorry

/-- The comparison from `X_red` to `X ×_S S_red` is a thickening: a surjective
closed immersion, not in general an isomorphism. -/
instance instIsThickening_reductionComparison {X S : Scheme.{u}} (f : X ⟶ S) :
    IsThickening (reductionComparison f) :=
  sorry

/-- Reduction of a locally finite type morphism remains locally of finite type. -/
instance instLocallyOfFiniteType_reductionMap {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] : LocallyOfFiniteType (Scheme.reductionMap f) :=
  sorry

/-- The reduction inclusion induces residue-field isomorphisms. -/
theorem isIso_reductionι_residueFieldMap (X : Scheme.{u})
    (x : Scheme.reduction X) :
    IsIso ((Scheme.reductionι X).residueFieldMap x) :=
  sorry

/-- Closed-immersion pushforward of an effective relative `r`-cycle remains
effective. -/
theorem effectivePushforward_mem {X X' S : Scheme.{u}} (fX : X ⟶ S)
    (fX' : X' ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType fX]
    [LocallyOfFiniteType fX'] (i : X ⟶ X') [IsClosedImmersion i]
    (hc : i ≫ fX' = fX) (r : ℕ) (α : effective fX r) :
    pushforward fX' i hc (α : Family fX r) ∈ effective fX' r :=
  sorry

/-- Pushforward of effective relative `r`-cycles along a closed immersion over
`S`. -/
def effectivePushforward {X X' S : Scheme.{u}} (fX : X ⟶ S) (fX' : X' ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType fX] [LocallyOfFiniteType fX']
    (i : X ⟶ X') [IsClosedImmersion i] (hc : i ≫ fX' = fX) (r : ℕ) :
    effective fX r →+ effective fX' r where
  toFun α :=
    ⟨pushforward fX' i hc (α : Family fX r),
      effectivePushforward_mem fX fX' i hc r α⟩
  map_zero' := sorry
  map_add' := sorry

/-- The underlying fibrewise family of `effectivePushforward` is family-level
pushforward. -/
theorem effectivePushforward_apply {X X' S : Scheme.{u}} (fX : X ⟶ S)
    (fX' : X' ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType fX]
    [LocallyOfFiniteType fX'] (i : X ⟶ X') [IsClosedImmersion i]
    (hc : i ≫ fX' = fX) (r : ℕ) (α : effective fX r) :
    (effectivePushforward fX fX' i hc r α : Family fX' r) =
      pushforward fX' i hc (α : Family fX r) :=
  sorry

/-- The inverse of pushforward along a thickening preserves effectiveness. -/
theorem isEffective_of_isEffective_pushforward {X X' S : Scheme.{u}}
    (fX : X ⟶ S) (fX' : X' ⟶ S) [IsLocallyNoetherian S]
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fX'] (i : X ⟶ X')
    [IsThickening i] (hc : i ≫ fX' = fX) {r : ℕ} {α : Family fX r}
    (hα : IsRelative α) :
    IsEffective (pushforward fX' i hc α) → IsEffective α :=
  sorry

/-- Pushforward of effective relative `r`-cycles along a thickening is
bijective. -/
theorem effectivePushforward_bijective {X X' S : Scheme.{u}} (fX : X ⟶ S)
    (fX' : X' ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType fX]
    [LocallyOfFiniteType fX'] (i : X ⟶ X') [IsThickening i]
    (hc : i ≫ fX' = fX) (r : ℕ) :
    Function.Bijective (effectivePushforward fX fX' i hc r) :=
  sorry

/-- Base change of effective relative cycles along the reduction inclusion is
bijective. -/
theorem effectiveBaseChange_reductionι_bijective {X S : Scheme.{u}}
    (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) :
    Function.Bijective (effectiveBaseChange f (Scheme.reductionι S) r) :=
  sorry

/-- Identification `z(X/S, r) ≃+ z(X_red / S_red, r)` of relative cycle groups,
as base change along `reductionι` inverted through pushforward along the
thickening `reductionComparison`. -/
def groupReductionEquiv {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) :
    group f r ≃+ group (Scheme.reductionMap f) r :=
  (AddEquiv.ofBijective (groupBaseChange f (Scheme.reductionι S) r)
      (groupBaseChange_bijective f (Scheme.reductionι S)
        (fun s' ↦ isIso_reductionι_residueFieldMap S s') r)).trans
    (AddEquiv.ofBijective
        (groupPushforward (Scheme.reductionMap f)
          (pullback.snd f (Scheme.reductionι S))
          (reductionComparison f) (reductionComparison_snd f) r)
        (groupPushforward_bijective (Scheme.reductionMap f)
          (pullback.snd f (Scheme.reductionι S))
          (reductionComparison f) (reductionComparison_snd f) r)).symm

/-- Pushforward along `reductionComparison` recovers base change along
`reductionι` from `groupReductionEquiv`. -/
theorem groupReductionEquiv_apply {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) (α : group f r) :
    groupPushforward (Scheme.reductionMap f) (pullback.snd f (Scheme.reductionι S))
        (reductionComparison f) (reductionComparison_snd f) r
        (groupReductionEquiv f r α) =
      groupBaseChange f (Scheme.reductionι S) r α :=
  sorry

/-- Identification `z^{eff}(X/S, r) ≃+ z^{eff}(X_red / S_red, r)` of effective
relative cycles, as effective base change along `reductionι` inverted through
effective pushforward along the thickening `reductionComparison`. -/
def effectiveReductionEquiv {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) :
    effective f r ≃+ effective (Scheme.reductionMap f) r :=
  (AddEquiv.ofBijective (effectiveBaseChange f (Scheme.reductionι S) r)
      (effectiveBaseChange_reductionι_bijective f r)).trans
    (AddEquiv.ofBijective
        (effectivePushforward (Scheme.reductionMap f)
          (pullback.snd f (Scheme.reductionι S))
          (reductionComparison f) (reductionComparison_snd f) r)
        (effectivePushforward_bijective (Scheme.reductionMap f)
          (pullback.snd f (Scheme.reductionι S))
          (reductionComparison f) (reductionComparison_snd f) r)).symm

/-- Effective pushforward along `reductionComparison` recovers effective base
change along `reductionι` from `effectiveReductionEquiv`. -/
theorem effectiveReductionEquiv_apply {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    (α : effective f r) :
    effectivePushforward (Scheme.reductionMap f)
        (pullback.snd f (Scheme.reductionι S))
        (reductionComparison f) (reductionComparison_snd f) r
        (effectiveReductionEquiv f r α) =
      effectiveBaseChange f (Scheme.reductionι S) r α :=
  sorry

/-- The big `h` topology restricted to schemes locally of finite type over `S`. -/
def locallyOfFiniteTypeOverHTopology (S : Scheme.{u}) :
    GrothendieckTopology (LocallyOfFiniteTypeOver S) :=
  (MorphismProperty.Over.forget (@LocallyOfFiniteType) ⊤ S).restrictedTopology
    ((Scheme.hPrecoverage.toGrothendieck).over S)

end AlgebraicGeometry.RelativeCycle

