module

public import stacks_project.Chap42.Definition_42_50_3_RationalBivariant
public import stacks_project.Chap42.Lemma_42_49_3_AtZero
public import stacks_project.Chap42.Lemma_42_50_2

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- Restriction of the deformation complex to the lifted zero fibre. -/
def zeroFiberRestriction
    {S : Scheme.{u}} {X : Over S} {W : Scheme.{u}}
    (b : W ⟶ ProjectiveLineFamily.space X)
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (Q : RingedSpace.ModuleDerived W.toRingedSpace) :
    RingedSpace.ModuleDerived X.left.toRingedSpace :=
  (RingedSpace.modulePullbackDerived
    (BivariantClass.GysinAtInfinity.zeroSectionLift X b).left.toShHom).obj Q

/-- `zeroFiberRestriction` is derived pullback along the lifted zero section. -/
theorem zeroFiberRestriction_def
    {S : Scheme.{u}} {X : Over S} {W : Scheme.{u}}
    (b : W ⟶ ProjectiveLineFamily.space X)
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (Q : RingedSpace.ModuleDerived W.toRingedSpace) :
    zeroFiberRestriction b Q =
      (RingedSpace.modulePullbackDerived
        (BivariantClass.GysinAtInfinity.zeroSectionLift X b).left.toShHom).obj Q := sorry

/-- Restriction of the deformation complex to the infinity fibre. -/
def infinityFiberRestriction
    {S : Scheme.{u}} {X : Over S} {W : Scheme.{u}}
    (b : W ⟶ ProjectiveLineFamily.space X)
    (Q : RingedSpace.ModuleDerived W.toRingedSpace) :
    RingedSpace.ModuleDerived
      (BivariantClass.GysinAtInfinity.infinityFiber X b).left.toRingedSpace :=
  (RingedSpace.modulePullbackDerived
    (BivariantClass.GysinAtInfinity.infinityInclusion X b).left.toShHom).obj Q

/-- `infinityFiberRestriction` is derived pullback along the infinity inclusion. -/
theorem infinityFiberRestriction_def
    {S : Scheme.{u}} {X : Over S} {W : Scheme.{u}}
    (b : W ⟶ ProjectiveLineFamily.space X)
    (Q : RingedSpace.ModuleDerived W.toRingedSpace) :
    infinityFiberRestriction b Q =
      (RingedSpace.modulePullbackDerived
        (BivariantClass.GysinAtInfinity.infinityInclusion X b).left.toShHom).obj Q := sorry

/-- Restriction of the deformation complex to the inverse image of the closed center in
the infinity fibre. -/
def infinityCenterRestriction
    {S : Scheme.{u}} {X : Over S} {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) (b : W ⟶ ProjectiveLineFamily.space X)
    (Q : RingedSpace.ModuleDerived W.toRingedSpace) :
    RingedSpace.ModuleDerived (infinityCenter i b).left.toRingedSpace :=
  (RingedSpace.modulePullbackDerived
    ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
        (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q

/-- `infinityCenterRestriction` is the pullback of the deformation complex to the
canonical infinity center. -/
theorem infinityCenterRestriction_def
    {S : Scheme.{u}} {X : Over S} {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) (b : W ⟶ ProjectiveLineFamily.space X)
    (Q : RingedSpace.ModuleDerived W.toRingedSpace) :
    infinityCenterRestriction i b Q =
      (RingedSpace.modulePullbackDerived
        ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
            (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q := sorry

/-- Projection from the inverse image of the affine-line part of a compactification to `X`. -/
def affineDeformationProjection
    {S : Scheme.{u}} {X : Over S} {W : Scheme.{u}}
    (b : W ⟶ ProjectiveLineFamily.space X) :
    (b ⁻¹ᵁ BivariantClass.GysinAtInfinity.affinePart X).toScheme ⟶ X.left :=
  (b ⁻¹ᵁ BivariantClass.GysinAtInfinity.affinePart X).ι ≫ b ≫
    pullback.fst X.hom (ProjectiveSpace.toBase 1 S)

/-- `affineDeformationProjection` is induced by the first projection of
`X ×ₛ ℙ¹ₛ`. -/
theorem affineDeformationProjection_def
    {S : Scheme.{u}} {X : Over S} {W : Scheme.{u}}
    (b : W ⟶ ProjectiveLineFamily.space X) :
    affineDeformationProjection b =
      (b ⁻¹ᵁ BivariantClass.GysinAtInfinity.affinePart X).ι ≫ b ≫
        pullback.fst X.hom (ProjectiveSpace.toBase 1 S) := sorry

/-- The restriction of a derived module along a specified subscheme morphism has the
selected vanishing or rank-bounded behavior. -/
def RestrictionCondition
    {X Y : Scheme.{u}} (j : Y ⟶ X)
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (p : ℕ) :
    RestrictionBehavior → Prop
  | .vanishing =>
      IsZero ((RingedSpace.modulePullbackDerived j.toShHom).obj E)
  | .rankBound =>
      Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
        ((RingedSpace.modulePullbackDerived j.toShHom).obj E) 0 p

/-- In the vanishing mode, `RestrictionCondition` says that the specified pullback is zero. -/
theorem restrictionCondition_vanishing_iff
    {X Y : Scheme.{u}} (j : Y ⟶ X)
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (p : ℕ) :
    RestrictionCondition j E p .vanishing ↔
      IsZero ((RingedSpace.modulePullbackDerived j.toShHom).obj E) := sorry

/-- In the rank-bounded mode, `RestrictionCondition` gives the source-prescribed
finite locally free module in degree zero. -/
theorem restrictionCondition_rankBound_iff
    {X Y : Scheme.{u}} (j : Y ⟶ X)
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (p : ℕ) :
    RestrictionCondition j E p .rankBound ↔
      Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
        ((RingedSpace.modulePullbackDerived j.toShHom).obj E) 0 p := sorry

/-- The Newton or Chern class of the deformation complex on the infinity center,
according to the off-center alternative in `Situation 42.50.1`. -/
noncomputable def infinityAmbientClass
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    (classes : ChernClass.Theory δ X.hom)
    (Q : RingedSpace.ModuleDerived W.toRingedSpace) (p : ℕ)
    (mode : RestrictionBehavior)
    (perfect : RingedSpace.ModuleDerived.IsPerfect (infinityCenterRestriction i b Q))
    (defined : ChernClass.Derived.IsDefined (infinityCenterRestriction i b Q)) :
    BivariantClass δ (𝟙 (infinityCenter i b)) (p : ℤ) :=
  match mode with
  | .vanishing =>
      ChernClass.Derived.newtonClass δ (infinityCenter i b).hom
        (classes.reanchor (infinityCenter i b)) (infinityCenterRestriction i b Q)
        perfect defined p
  | .rankBound =>
      ChernClass.Derived.totalClass δ (infinityCenter i b).hom
        (classes.reanchor (infinityCenter i b)) (infinityCenterRestriction i b Q)
        perfect defined p

/-- `infinityAmbientClass` selects the Newton class in the vanishing case and the
total Chern class in the rank-bound case. -/
theorem infinityAmbientClass_spec
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    (classes : ChernClass.Theory δ X.hom)
    (Q : RingedSpace.ModuleDerived W.toRingedSpace) (p : ℕ)
    (mode : RestrictionBehavior)
    (perfect : RingedSpace.ModuleDerived.IsPerfect (infinityCenterRestriction i b Q))
    (defined : ChernClass.Derived.IsDefined (infinityCenterRestriction i b Q)) :
    infinityAmbientClass i b classes Q p mode perfect defined =
      match mode with
      | .vanishing =>
          ChernClass.Derived.newtonClass δ (infinityCenter i b).hom
            (classes.reanchor (infinityCenter i b)) (infinityCenterRestriction i b Q)
            perfect defined p
      | .rankBound =>
          ChernClass.Derived.totalClass δ (infinityCenter i b).hom
            (classes.reanchor (infinityCenter i b)) (infinityCenterRestriction i b Q)
            perfect defined p := sorry

/-- The blowing-up, deformation complex `Q`, closed infinity subscheme `T`, and its
clopen part `T'` used in Lemma 42.50.2. -/
structure ClassConstruction
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (mode : RestrictionBehavior) (situation : Situation S δ X i E p mode) where
  /-- The proper compactification carrying the deformation complex `Q`. -/
  W : Scheme.{u}
  /-- The compactification morphism to `X ×ₛ ℙ¹ₛ`. -/
  b : W ⟶ ProjectiveLineFamily.space X
  /-- The compactification morphism is proper. -/
  [b_isProper : IsProper b]
  /-- The compactification agrees with the original affine-line family away from infinity. -/
  [b_affinePart_isIso : IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
  /-- The perfect deformation complex `Q` on `W`. -/
  Q : RingedSpace.ModuleDerived W.toRingedSpace
  /-- The deformation complex is perfect. -/
  Q_isPerfect : RingedSpace.ModuleDerived.IsPerfect Q
  /-- Over the affine-line part, `Q` is the prescribed pullback deformation of `E`. -/
  affineDeformation_iso : IsIsomorphic
    ((RingedSpace.modulePullbackDerived
      (b ⁻¹ᵁ BivariantClass.GysinAtInfinity.affinePart X).ι.toShHom).obj Q)
    ((RingedSpace.modulePullbackDerived (affineDeformationProjection b).toShHom).obj E)
  /-- The zero-fibre restriction of `Q` is the original complex `E`. -/
  zeroFiber_iso : IsIsomorphic (zeroFiberRestriction b Q) E
  /-- The closed subscheme `T` of the infinity fibre constructed in Lemma 42.50.2. -/
  T : Scheme.{u}
  /-- The inclusion of `T` into the infinity fibre. -/
  t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left
  /-- The morphism `T ⟶ W∞` is a closed immersion. -/
  [t_isClosedImmersion : IsClosedImmersion t]
  /-- The clopen part `T'` on which `Q` has the source-prescribed behavior. -/
  T' : Scheme.{u}
  /-- The inclusion of `T'` into `T`. -/
  t' : T' ⟶ T
  /-- The morphism `T' ⟶ T` is an open immersion. -/
  [t'_isOpenImmersion : IsOpenImmersion t']
  /-- The morphism `T' ⟶ T` is a closed immersion. -/
  [t'_isClosedImmersion : IsClosedImmersion t']
  /-- The closed subscheme `T` contains every point of the infinity fibre over `X \ Z`. -/
  containsComplement :
    (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
        (Set.range i.base)ᶜ ⊆ Set.range t.base
  /-- The map `W∞ ⟶ X` becomes an isomorphism over `X \ Z`. -/
  infinityFiber_complement_isIso : IsIso
    (pullback.snd (BivariantClass.GysinAtInfinity.infinityToX X b).left
      (openComplement i).ι)
  /-- The map `T ⟶ X` becomes an isomorphism over `X \ Z`. -/
  T_complement_isIso : IsIso
    (pullback.snd (t ≫ (BivariantClass.GysinAtInfinity.infinityToX X b).left)
      (openComplement i).ι)
  /-- The map `T' ⟶ X` becomes an isomorphism over `X \ Z`. -/
  T'_complement_isIso : IsIso
    (pullback.snd (t' ≫ t ≫
      (BivariantClass.GysinAtInfinity.infinityToX X b).left) (openComplement i).ι)
  /-- The restriction of `Q` to `T'` has the vanishing or rank-bounded behavior from
  Situation 42.50.1. -/
  onT' : RestrictionCondition
    (t' ≫ t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left) Q p mode
  /-- The restriction of `Q` to the infinity center is perfect. -/
  infinityCenter_isPerfect :
    RingedSpace.ModuleDerived.IsPerfect (infinityCenterRestriction i b Q)
  /-- The derived Chern classes of `Q` on the infinity center are defined. -/
  infinityCenter_isDefined :
    ChernClass.Derived.IsDefined (infinityCenterRestriction i b Q)
  /-- The inverse image of the closed center is closed in the infinity fibre. -/
  [infinityCenter_isClosedImmersion : IsClosedImmersion
    (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left]
  /-- The localized Newton or Chern class on the inverse image of `Z` at infinity. -/
  localizedAtInfinity : BivariantClass δ
    (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) (p : ℤ)
  /-- The infinity class is the localized extension of the class of `Q` prescribed by
  the vanishing or rank-bound alternative. -/
  localizedAtInfinity_spec : IsInfinityLocalizedExtension δ i b (t' ≫ t) (p : ℤ)
    (infinityAmbientClass i b classes Q p mode
      infinityCenter_isPerfect infinityCenter_isDefined) localizedAtInfinity

namespace ClassConstruction

/-- Build Lemma 42.50.2 construction data from an explicit deformation complex and its
localized infinity class. -/
def ofDeformation
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W T T' : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (mode : RestrictionBehavior) (situation : Situation S δ X i E p mode)
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (Q : RingedSpace.ModuleDerived W.toRingedSpace)
    (Q_isPerfect : RingedSpace.ModuleDerived.IsPerfect Q)
    (affineDeformation_iso : IsIsomorphic
      ((RingedSpace.modulePullbackDerived
        (b ⁻¹ᵁ BivariantClass.GysinAtInfinity.affinePart X).ι.toShHom).obj Q)
      ((RingedSpace.modulePullbackDerived (affineDeformationProjection b).toShHom).obj E))
    (zeroFiber_iso : IsIsomorphic (zeroFiberRestriction b Q) E)
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t]
    (t' : T' ⟶ T) [IsOpenImmersion t']
    [IsClosedImmersion t']
    (containsComplement :
      (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
          (Set.range i.base)ᶜ ⊆ Set.range t.base)
    (infinityFiber_complement_isIso : IsIso
      (pullback.snd (BivariantClass.GysinAtInfinity.infinityToX X b).left
        (openComplement i).ι))
    (T_complement_isIso : IsIso
      (pullback.snd (t ≫ (BivariantClass.GysinAtInfinity.infinityToX X b).left)
        (openComplement i).ι))
    (T'_complement_isIso : IsIso
      (pullback.snd (t' ≫ t ≫
        (BivariantClass.GysinAtInfinity.infinityToX X b).left) (openComplement i).ι))
    (onT' : RestrictionCondition
      (t' ≫ t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left) Q p mode)
    (infinityCenter_isPerfect :
      RingedSpace.ModuleDerived.IsPerfect (infinityCenterRestriction i b Q))
    (infinityCenter_isDefined :
      ChernClass.Derived.IsDefined (infinityCenterRestriction i b Q))
    [IsClosedImmersion
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left]
    (localizedAtInfinity : BivariantClass δ
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) (p : ℤ))
    (localizedAtInfinity_spec : IsInfinityLocalizedExtension δ i b (t' ≫ t) (p : ℤ)
      (infinityAmbientClass i b classes Q p mode
        infinityCenter_isPerfect infinityCenter_isDefined) localizedAtInfinity) :
    ClassConstruction δ i classes E p mode situation :=
  { W := W
    b := b
    Q := Q
    Q_isPerfect := Q_isPerfect
    affineDeformation_iso := affineDeformation_iso
    zeroFiber_iso := zeroFiber_iso
    T := T
    t := t
    T' := T'
    t' := t'
    containsComplement := containsComplement
    infinityFiber_complement_isIso := infinityFiber_complement_isIso
    T_complement_isIso := T_complement_isIso
    T'_complement_isIso := T'_complement_isIso
    onT' := onT'
    infinityCenter_isPerfect := infinityCenter_isPerfect
    infinityCenter_isDefined := infinityCenter_isDefined
    localizedAtInfinity := localizedAtInfinity
    localizedAtInfinity_spec := localizedAtInfinity_spec }

/-- The concrete localized bivariant class obtained from the deformation at zero. -/
def result
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    {classes : ChernClass.Theory δ X.hom}
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    {mode : RestrictionBehavior} {situation : Situation S δ X i E p mode}
    (construction : ClassConstruction δ i classes E p mode situation) :
    BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ) :=
  @classAtZero S inferInstance δ inferInstance X inferInstance Z construction.W i
    inferInstance construction.b construction.b_isProper construction.b_affinePart_isIso
    (p : ℤ) construction.localizedAtInfinity

/-- The result of any Lemma 42.50.2 construction has the prescribed ambient pushforward. -/
theorem result_pushforward_eq
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    {classes : ChernClass.Theory δ X.hom}
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    {mode : RestrictionBehavior} {situation : Situation S δ X i E p mode}
    (construction : ClassConstruction δ i classes E p mode situation) :
    BivariantClass.pushforwardToTarget δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ) construction.result =
      match mode with
      | .vanishing =>
          ChernClass.Derived.newtonClass δ X.hom classes E situation.perfect
            situation.isDefined p
      | .rankBound =>
          ChernClass.Derived.totalClass δ X.hom classes E situation.perfect
            situation.isDefined p := sorry

/-- Lemma 42.50.2 supplies a deformation construction satisfying the full affine and
infinity-fibre specification. -/
theorem construction_nonempty
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (mode : RestrictionBehavior) (situation : Situation S δ X i E p mode) :
    Nonempty (ClassConstruction δ i classes E p mode situation) := sorry

/-- Comparison data for passing from one valid Lemma 42.50.2 construction to a
modification of it. -/
structure ConstructionModification
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    {classes : ChernClass.Theory δ X.hom}
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    {mode : RestrictionBehavior} {situation : Situation S δ X i E p mode}
    (a b : ClassConstruction δ i classes E p mode situation) where
  /-- The first infinity fibre is locally of finite type over `S`. -/
  [a_infinityFiber_finiteType : LocallyOfFiniteType
    (BivariantClass.GysinAtInfinity.infinityFiber X a.b).hom]
  /-- The second infinity fibre is locally of finite type over `S`. -/
  [b_infinityFiber_finiteType : LocallyOfFiniteType
    (BivariantClass.GysinAtInfinity.infinityFiber X b.b).hom]
  /-- The first infinity center is locally of finite type over `S`. -/
  [a_infinityCenter_finiteType : LocallyOfFiniteType (infinityCenter i a.b).hom]
  /-- The second infinity center is locally of finite type over `S`. -/
  [b_infinityCenter_finiteType : LocallyOfFiniteType (infinityCenter i b.b).hom]
  /-- The proper comparison of infinity fibres, directed from `b` to `a`. -/
  gInf : BivariantClass.GysinAtInfinity.infinityFiber X b.b ⟶
    BivariantClass.GysinAtInfinity.infinityFiber X a.b
  /-- The comparison of infinity fibres is proper. -/
  [gInf_isProper : IsProper gInf.left]
  /-- The comparison is compatible with the maps of infinity fibres to `X`. -/
  overX : gInf ≫ BivariantClass.GysinAtInfinity.infinityToX X a.b =
    BivariantClass.GysinAtInfinity.infinityToX X b.b
  /-- The localized infinity class for `b` is the restriction of that for `a`. -/
  localizedPullback : b.localizedAtInfinity = BivariantClass.restrict δ
    (infinityCenterMap i a.b b.b gInf overX)
    (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b.b)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))
    gInf (infinityCenterMap_isPullback i a.b b.b gInf overX) (p : ℤ)
    a.localizedAtInfinity
  /-- Proper pushforward of the degree-zero Gysin class for `b` is the Gysin class for `a`. -/
  gysinPushforward : BivariantClass.pushforward δ gInf
    (BivariantClass.GysinAtInfinity.infinityToX X a.b) 0
    (overX.symm ▸ @BivariantClass.gysinAtInfinity S b.W inferInstance δ
      inferInstance X inferInstance b.b b.b_isProper b.b_affinePart_isIso) =
      @BivariantClass.gysinAtInfinity S a.W inferInstance δ inferInstance X
        inferInstance a.b a.b_isProper a.b_affinePart_isIso

/-- Build modification data from the comparison map and its two compatibility laws. -/
def ConstructionModification.ofInfinityComparison
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    {classes : ChernClass.Theory δ X.hom}
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    {mode : RestrictionBehavior} {situation : Situation S δ X i E p mode}
    (a b : ClassConstruction δ i classes E p mode situation)
    [LocallyOfFiniteType (BivariantClass.GysinAtInfinity.infinityFiber X a.b).hom]
    [LocallyOfFiniteType (BivariantClass.GysinAtInfinity.infinityFiber X b.b).hom]
    [LocallyOfFiniteType (infinityCenter i a.b).hom]
    [LocallyOfFiniteType (infinityCenter i b.b).hom]
    (gInf : BivariantClass.GysinAtInfinity.infinityFiber X b.b ⟶
      BivariantClass.GysinAtInfinity.infinityFiber X a.b)
    [IsProper gInf.left]
    (overX : gInf ≫ BivariantClass.GysinAtInfinity.infinityToX X a.b =
      BivariantClass.GysinAtInfinity.infinityToX X b.b)
    (localizedPullback : b.localizedAtInfinity = BivariantClass.restrict δ
      (infinityCenterMap i a.b b.b gInf overX)
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b.b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))
      gInf (infinityCenterMap_isPullback i a.b b.b gInf overX) (p : ℤ)
      a.localizedAtInfinity)
    (gysinPushforward : BivariantClass.pushforward δ gInf
      (BivariantClass.GysinAtInfinity.infinityToX X a.b) 0
      (overX.symm ▸ @BivariantClass.gysinAtInfinity S b.W inferInstance δ
        inferInstance X inferInstance b.b b.b_isProper b.b_affinePart_isIso) =
        @BivariantClass.gysinAtInfinity S a.W inferInstance δ inferInstance X
          inferInstance a.b a.b_isProper a.b_affinePart_isIso) :
    ConstructionModification a b :=
  { gInf := gInf
    overX := overX
    localizedPullback := localizedPullback
    gysinPushforward := gysinPushforward }

/-- A third valid construction together with modifications to two given constructions. -/
structure CommonModification
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    {classes : ChernClass.Theory δ X.hom}
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    {mode : RestrictionBehavior} {situation : Situation S δ X i E p mode}
    (a b : ClassConstruction δ i classes E p mode situation) where
  /-- The construction dominating both given constructions. -/
  common : ClassConstruction δ i classes E p mode situation
  /-- The modification from the common construction to `a`. -/
  toLeft : ConstructionModification a common
  /-- The modification from the common construction to `b`. -/
  toRight : ConstructionModification b common

/-- Bundle a common construction and its two modification comparisons. -/
def CommonModification.ofComparisons
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    {classes : ChernClass.Theory δ X.hom}
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    {mode : RestrictionBehavior} {situation : Situation S δ X i E p mode}
    (a b common : ClassConstruction δ i classes E p mode situation)
    (toLeft : ConstructionModification a common)
    (toRight : ConstructionModification b common) : CommonModification a b :=
  { common := common, toLeft := toLeft, toRight := toRight }

/-- A valid modification induces equality of the resulting classes at zero. -/
theorem result_eq_of_modification
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    {classes : ChernClass.Theory δ X.hom}
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    {mode : RestrictionBehavior} {situation : Situation S δ X i E p mode}
    (a b : ClassConstruction δ i classes E p mode situation)
    (comparison : ConstructionModification a b) : b.result = a.result := sorry

/-- Two constructions with a common modification give the same class at zero. -/
theorem result_eq_of_commonModification
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    {classes : ChernClass.Theory δ X.hom}
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    {mode : RestrictionBehavior} {situation : Situation S δ X i E p mode}
    (a b : ClassConstruction δ i classes E p mode situation)
    (comparison : CommonModification a b) : a.result = b.result := sorry

/-- Any two fully specified Lemma 42.50.2 constructions admit a common modification. -/
theorem commonModification_nonempty
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    {classes : ChernClass.Theory δ X.hom}
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    {mode : RestrictionBehavior} {situation : Situation S δ X i E p mode}
    (a b : ClassConstruction δ i classes E p mode situation) :
    Nonempty (CommonModification a b) := sorry

/-- The class at zero is independent of all exact Lemma 42.50.2 constructions. -/
theorem result_eq
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    {classes : ChernClass.Theory δ X.hom}
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    {mode : RestrictionBehavior} {situation : Situation S δ X i E p mode}
    (a b : ClassConstruction δ i classes E p mode situation) :
    a.result = b.result := sorry

/-- A bivariant class is the canonical result of Lemma 42.50.2 when it is represented
by one fully specified deformation construction. -/
def IsResult
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (mode : RestrictionBehavior) (situation : Situation S δ X i E p mode)
    (localized : BivariantClass δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ)) : Prop :=
  ∃ construction : ClassConstruction δ i classes E p mode situation,
    localized = construction.result

/-- The construction-result predicate is represented by an explicit deformation. -/
theorem isResult_iff
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (mode : RestrictionBehavior) (situation : Situation S δ X i E p mode)
    (localized : BivariantClass δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ)) :
    IsResult classes E p mode situation localized ↔
      ∃ construction : ClassConstruction δ i classes E p mode situation,
        localized = construction.result := sorry

/-- Two bivariant classes represented by valid Lemma 42.50.2 constructions are equal. -/
theorem isResult_unique
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (mode : RestrictionBehavior) (situation : Situation S δ X i E p mode)
    {a b : BivariantClass δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ)}
    (ha : IsResult classes E p mode situation a)
    (hb : IsResult classes E p mode situation b) : a = b := sorry

end ClassConstruction

/-- The localized Newton class obtained from one explicit Lemma 42.50.2 construction. -/
def newtonClassOfConstruction
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E)) (finiteness : TechnicalCondition X E)
    (p : ℕ)
    (construction : ClassConstruction δ i classes E p .vanishing
      (Situation.vanishing perfect vanishing finiteness)) :
    BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ) :=
  construction.result

/-- The Newton class from an explicit construction satisfies the canonical result predicate. -/
theorem newtonClassOfConstruction_spec
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E)) (finiteness : TechnicalCondition X E)
    (p : ℕ)
    (construction : ClassConstruction δ i classes E p .vanishing
      (Situation.vanishing perfect vanishing finiteness)) :
    ClassConstruction.IsResult classes E p .vanishing
      (Situation.vanishing perfect vanishing finiteness)
      (newtonClassOfConstruction i classes E perfect vanishing finiteness p construction) := sorry

/-- The canonical localized Newton class defined by the construction of Lemma 42.50.2. -/
noncomputable def newtonClass
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E)) (finiteness : TechnicalCondition X E)
    (p : ℕ) :
    BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ) :=
  Classical.epsilon (ClassConstruction.IsResult classes E p .vanishing
    (Situation.vanishing perfect vanishing finiteness))

/-- The canonical localized Newton class is represented by the full deformation
construction of Lemma 42.50.2. -/
theorem newtonClass_spec
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E)) (finiteness : TechnicalCondition X E)
    (p : ℕ) :
    ClassConstruction.IsResult classes E p .vanishing
      (Situation.vanishing perfect vanishing finiteness)
      (newtonClass i classes E perfect vanishing finiteness p) := sorry

/-- Every explicitly constructed localized Newton class equals the canonical class. -/
theorem newtonClass_eq_ofConstruction
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E)) (finiteness : TechnicalCondition X E)
    (p : ℕ)
    (construction : ClassConstruction δ i classes E p .vanishing
      (Situation.vanishing perfect vanishing finiteness)) :
    newtonClass i classes E perfect vanishing finiteness p =
      newtonClassOfConstruction i classes E perfect vanishing finiteness p construction := sorry

/-- The localized Newton class pushes forward to the ambient derived Newton class. -/
theorem newtonClass_pushforward
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E)) (finiteness : TechnicalCondition X E)
    (p : ℕ) :
    BivariantClass.pushforwardToTarget δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ)
        (newtonClass i classes E perfect vanishing finiteness p) =
      ChernClass.Derived.newtonClass δ X.hom classes E perfect
        ((Situation.vanishing perfect vanishing finiteness :
          Situation S δ X i E p .vanishing).isDefined) p := sorry

/-- The localized Chern character with degree-`p` component `Pₚ(Z ⟶ X, E) / p!`. -/
def character
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E)) (finiteness : TechnicalCondition X E) :
    BivariantClass.Nonnegative.RationalCompletion δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) :=
  fun p ↦ TensorProduct.tmul ℤ
    (newtonClass i classes E perfect vanishing finiteness p) ((p.factorial : ℚ)⁻¹)

/-- Evaluation of the localized Chern character gives `Pₚ(Z ⟶ X, E) / p!`. -/
theorem character_apply
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E)) (finiteness : TechnicalCondition X E)
    (p : ℕ) :
    character i classes E perfect vanishing finiteness p =
      TensorProduct.tmul ℤ (newtonClass i classes E perfect vanishing finiteness p)
        ((p.factorial : ℚ)⁻¹) := sorry

/-- The localized `p`th Chern class obtained from one explicit Lemma 42.50.2
construction. -/
def chernClassOfConstruction
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E) (p : ℕ)
    (rankBound : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      (restrictAway i E) 0 p) (finiteness : TechnicalCondition X E)
    (construction : ClassConstruction δ i classes E p .rankBound
      (Situation.rankBound perfect rankBound finiteness)) :
    BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ) :=
  construction.result

/-- The arbitrary-construction Chern class satisfies the canonical result predicate. -/
theorem chernClassOfConstruction_spec
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E) (p : ℕ)
    (rankBound : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      (restrictAway i E) 0 p) (finiteness : TechnicalCondition X E)
    (construction : ClassConstruction δ i classes E p .rankBound
      (Situation.rankBound perfect rankBound finiteness)) :
    ClassConstruction.IsResult classes E p .rankBound
      (Situation.rankBound perfect rankBound finiteness)
      (chernClassOfConstruction i classes E perfect p rankBound finiteness construction) := sorry

/-- The canonical localized `p`th Chern class defined by Lemma 42.50.2. -/
noncomputable def chernClass
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E) (p : ℕ)
    (rankBound : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      (restrictAway i E) 0 p) (finiteness : TechnicalCondition X E) :
    BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ) :=
  Classical.epsilon (ClassConstruction.IsResult classes E p .rankBound
    (Situation.rankBound perfect rankBound finiteness))

/-- The canonical localized Chern class is represented by the full deformation
construction of Lemma 42.50.2. -/
theorem chernClass_spec
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E) (p : ℕ)
    (rankBound : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      (restrictAway i E) 0 p) (finiteness : TechnicalCondition X E) :
    ClassConstruction.IsResult classes E p .rankBound
      (Situation.rankBound perfect rankBound finiteness)
      (chernClass i classes E perfect p rankBound finiteness) := sorry

/-- Every explicitly constructed localized Chern class equals the canonical class. -/
theorem chernClass_eq_ofConstruction
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E) (p : ℕ)
    (rankBound : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      (restrictAway i E) 0 p) (finiteness : TechnicalCondition X E)
    (construction : ClassConstruction δ i classes E p .rankBound
      (Situation.rankBound perfect rankBound finiteness)) :
    chernClass i classes E perfect p rankBound finiteness =
      chernClassOfConstruction i classes E perfect p rankBound finiteness construction := sorry

/-- The localized Chern class pushes forward to the ambient derived Chern class. -/
theorem chernClass_pushforward
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E) (p : ℕ)
    (rankBound : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      (restrictAway i E) 0 p) (finiteness : TechnicalCondition X E) :
    BivariantClass.pushforwardToTarget δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ)
        (chernClass i classes E perfect p rankBound finiteness) =
      ChernClass.Derived.totalClass δ X.hom classes E perfect
        ((Situation.rankBound perfect rankBound finiteness :
          Situation S δ X i E p .rankBound).isDefined) p := sorry

end AlgebraicGeometry.LocalizedChern
