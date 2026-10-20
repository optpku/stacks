module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Transport
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.Scheme.Seminormal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.WeakNormalization.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.LocallyNoetherian

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
  @LocallyOfFiniteType.isLocallyNoetherian X.left S X.hom X.prop
    ‹IsLocallyNoetherian S›

/-- The identity-functor image of a locally finite type scheme over a locally
Noetherian base is locally Noetherian. -/
instance instIsLocallyNoetherian_id_left {S : Scheme.{u}} [IsLocallyNoetherian S]
    (X : LocallyOfFiniteTypeOver S) :
    IsLocallyNoetherian ((𝟭 Scheme).obj X.left) :=
  instIsLocallyNoetherian_left X

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

/-- Weakly normal finite type schemes over a locally Noetherian base, obtained by
requiring the locally finite type structure morphism to be quasi-compact. -/
abbrev WeaklyNormalFiniteTypeOver (S : Scheme.{u}) [IsLocallyNoetherian S] :=
  ObjectProperty.FullSubcategory fun (X : WeaklyNormalOver S) => QuasiCompact X.obj.hom

/-- The canonical inclusion of weakly normal finite type schemes into locally
finite type schemes over the same base. -/
abbrev WeaklyNormalFiniteTypeOver.ι (S : Scheme.{u}) [IsLocallyNoetherian S] :
    WeaklyNormalFiniteTypeOver S ⥤ LocallyOfFiniteTypeOver S :=
  (ObjectProperty.ι fun (X : WeaklyNormalOver S) => QuasiCompact X.obj.hom) ⋙
    WeaklyNormalOver.ι S

/-- Morphisms in `LocallyOfFiniteTypeOver S` are locally of finite type. -/
instance instLocallyOfFiniteType_overHom {S : Scheme.{u}}
    {X Y : LocallyOfFiniteTypeOver S} (φ : X ⟶ Y) :
    LocallyOfFiniteType φ.left :=
  @locallyOfFiniteType_of_comp X.left Y.left S φ.left Y.hom
    ((MorphismProperty.Over.w φ).symm ▸ X.prop)

/-- The associator for a morphism of locally finite type `S`-schemes is a
morphism over the source. -/
theorem effectiveFunctor_map_over {X S : Scheme.{u}} (f : X ⟶ S)
    {S' S'' : LocallyOfFiniteTypeOver S} (φ : S'' ⟶ S') :
    ((pullbackLeftPullbackSndIso f S'.hom φ.left ≪≫
          pullback.congrHom rfl (MorphismProperty.Over.w φ)).hom) ≫
        pullback.snd f S''.hom =
      pullback.snd (pullback.snd f S'.hom) φ.left :=
  sorry

/-- Base change followed by canonical pullback transport acts additively on effective cycles. -/
def effectiveFunctor_map {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    {S' S'' : LocallyOfFiniteTypeOver S} (φ : S'' ⟶ S') :
    effective (pullback.snd f S'.hom) r →+
      effective (pullback.snd f S''.hom) r :=
  (@effectiveMapOfIsoOver _ _ _ _ _ _
    (MorphismProperty.pullback_snd (pullback.snd f S'.hom) φ.left
      (MorphismProperty.pullback_snd f S'.hom ‹LocallyOfFiniteType f›))
    (MorphismProperty.pullback_snd f S''.hom ‹LocallyOfFiniteType f›)
    ((pullbackLeftPullbackSndIso f S'.hom φ.left ≪≫
      pullback.congrHom rfl (MorphismProperty.Over.w φ)).hom) inferInstance
    (effectiveFunctor_map_over f φ) r).comp
      (effectiveBaseChange (pullback.snd f S'.hom) φ.left r)

/-- Effective-cycle base change along an identity morphism is the identity. -/
theorem effectiveFunctor_map_id {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    (S' : LocallyOfFiniteTypeOver S) :
    effectiveFunctor_map f r (𝟙 S') = AddMonoidHom.id _ := sorry

/-- Effective-cycle base change respects composition of morphisms of bases. -/
theorem effectiveFunctor_map_comp {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    {S' S'' T : LocallyOfFiniteTypeOver S} (φ : S'' ⟶ S') (ψ : T ⟶ S'') :
    effectiveFunctor_map f r (ψ ≫ φ) =
      (effectiveFunctor_map f r ψ).comp (effectiveFunctor_map f r φ) := sorry

/-- The contravariant functor `S' ↦ z^{eff}(S' ×_S X / S', r)` on schemes
locally of finite type over `S`. -/
def effectiveFunctor {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) :
    (LocallyOfFiniteTypeOver S)ᵒᵖ ⥤ Type u where
  obj S' := effective (pullback.snd f S'.unop.hom) r
  map φ := TypeCat.ofHom (effectiveFunctor_map f r φ.unop).toFun
  map_id S' := by
    change TypeCat.ofHom (effectiveFunctor_map f r (𝟙 S'.unop)).toFun = _
    rw [effectiveFunctor_map_id]
    rfl
  map_comp φ ψ := by
    change TypeCat.ofHom (effectiveFunctor_map f r (ψ.unop ≫ φ.unop)).toFun = _
    rw [effectiveFunctor_map_comp]
    rfl

/-- Evaluating `effectiveFunctor` at `S'` recovers `z^{eff}(S' ×_S X / S', r)`. -/
theorem effectiveFunctor_obj {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    (S' : LocallyOfFiniteTypeOver S) :
    (effectiveFunctor f r).obj (op S') =
      effective (pullback.snd f S'.hom) r :=
  rfl

/-- The action of `effectiveFunctor` on a morphism of bases is
`effectiveFunctor_map`. -/
theorem effectiveFunctor_map_apply {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    {S' S'' : LocallyOfFiniteTypeOver S} (φ : S'' ⟶ S')
    (α : effective (pullback.snd f S'.hom) r) :
    (effectiveFunctor f r).map φ.op α = effectiveFunctor_map f r φ α :=
  rfl

/-- The restriction of `effectiveFunctor` to seminormal locally finite type
`S`-schemes. -/
def effectiveFunctorSeminormal {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) :
    (SeminormalOver S)ᵒᵖ ⥤ Type u :=
  (SeminormalOver.ι S).op ⋙ effectiveFunctor f r

/-- The restriction of `effectiveFunctor` to weakly normal finite type
`S`-schemes. -/
def effectiveFunctorWeaklyNormal {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) :
    (WeaklyNormalFiniteTypeOver S)ᵒᵖ ⥤ Type u :=
  (WeaklyNormalFiniteTypeOver.ι S).op ⋙ effectiveFunctor f r

end AlgebraicGeometry.RelativeCycle
