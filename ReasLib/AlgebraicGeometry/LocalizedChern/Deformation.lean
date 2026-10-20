/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.GraphClass
public import ReasLib.AlgebraicGeometry.BivariantClass.LocalizedExtension
public import ReasLib.AlgebraicGeometry.BivariantClass.GysinAtInfinity.Pushforward
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.EnvelopeDescent

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
        (BivariantClass.GysinAtInfinity.zeroSectionLift X b).left.toShHom).obj Q := rfl

/-- Restriction of the deformation complex to the inverse image of the closed center in
the infinity fibre. -/
def infinityCenterRestriction
    {S : Scheme.{u}} {X : Over S} {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) (b : W ⟶ ProjectiveLineFamily.space X)
    (Q : RingedSpace.ModuleDerived W.toRingedSpace) :
    RingedSpace.ModuleDerived ((pullback (BivariantClass.GysinAtInfinity.infinityToX X b)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))).left.toRingedSpace :=
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
            (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q := rfl

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
        pullback.fst X.hom (ProjectiveSpace.toBase 1 S) := rfl

/-- The restriction of a derived module along a specified subscheme morphism has the
selected vanishing or rank-bounded behavior. -/
def RestrictionCondition
    {X Y : Scheme.{u}} (j : Y ⟶ X)
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (p : ℕ)
    (mode : RestrictionBehavior) : Prop :=
  match mode.isRankBound with
  | false =>
      IsZero ((RingedSpace.modulePullbackDerived j.toShHom).obj E)
  | true =>
      Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
        ((RingedSpace.modulePullbackDerived j.toShHom).obj E) 0 p

/-- In the vanishing mode, `RestrictionCondition` says that the specified pullback is zero. -/
theorem restrictionCondition_vanishing_iff
    {X Y : Scheme.{u}} (j : Y ⟶ X)
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (p : ℕ) :
    RestrictionCondition j E p .vanishing ↔
      IsZero ((RingedSpace.modulePullbackDerived j.toShHom).obj E) := Iff.rfl

/-- In the rank-bounded mode, `RestrictionCondition` gives a
finite locally free module in degree zero. -/
theorem restrictionCondition_rankBound_iff
    {X Y : Scheme.{u}} (j : Y ⟶ X)
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (p : ℕ) :
    RestrictionCondition j E p .rankBound ↔
      Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
        ((RingedSpace.modulePullbackDerived j.toShHom).obj E) 0 p := Iff.rfl

/-- The Newton or Chern class of the deformation complex on the infinity center,
according to the selected off-center behavior. -/
noncomputable def infinityAmbientClass
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i] (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    (classes : ChernClass.Theory δ X.hom)
    (Q : RingedSpace.ModuleDerived W.toRingedSpace) (p : ℕ)
    (mode : RestrictionBehavior)
    (perfect : RingedSpace.ModuleDerived.IsPerfect (infinityCenterRestriction i b Q))
    (defined : ChernClass.Derived.IsDefined (infinityCenterRestriction i b Q)) :
    BivariantClass δ (𝟙 ((pullback (BivariantClass.GysinAtInfinity.infinityToX X b)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)))) (p : ℤ) :=
  match mode.isRankBound with
  | false =>
      ChernClass.Derived.newtonClass δ ((pullback (BivariantClass.GysinAtInfinity.infinityToX X b)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))).hom
        (classes.reanchor ((pullback (BivariantClass.GysinAtInfinity.infinityToX X b)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)))) (infinityCenterRestriction i b Q)
        perfect defined p
  | true =>
      ChernClass.Derived.totalClass δ ((pullback (BivariantClass.GysinAtInfinity.infinityToX X b)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))).hom
        (classes.reanchor ((pullback (BivariantClass.GysinAtInfinity.infinityToX X b)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)))) (infinityCenterRestriction i b Q)
        perfect defined p

/-- `infinityAmbientClass` selects the Newton class in the vanishing case and the
total Chern class in the rank-bound case. -/
theorem infinityAmbientClass_spec
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i] (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    (classes : ChernClass.Theory δ X.hom)
    (Q : RingedSpace.ModuleDerived W.toRingedSpace) (p : ℕ)
    (mode : RestrictionBehavior)
    (perfect : RingedSpace.ModuleDerived.IsPerfect (infinityCenterRestriction i b Q))
    (defined : ChernClass.Derived.IsDefined (infinityCenterRestriction i b Q)) :
    infinityAmbientClass i b classes Q p mode perfect defined =
      match mode.isRankBound with
      | false =>
          ChernClass.Derived.newtonClass δ ((pullback (BivariantClass.GysinAtInfinity.infinityToX X b)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))).hom
            (classes.reanchor ((pullback (BivariantClass.GysinAtInfinity.infinityToX X b)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)))) (infinityCenterRestriction i b Q)
            perfect defined p
      | true =>
          ChernClass.Derived.totalClass δ ((pullback (BivariantClass.GysinAtInfinity.infinityToX X b)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))).hom
            (classes.reanchor ((pullback (BivariantClass.GysinAtInfinity.infinityToX X b)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)))) (infinityCenterRestriction i b Q)
            perfect defined p := rfl

/-- A proper deformation with a perfect complex, a closed infinity subscheme,
a clopen vanishing or rank-bound locus, and its localized infinity class. -/
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
  /-- A closed subscheme of the infinity fibre. -/
  T : Scheme.{u}
  /-- The inclusion of `T` into the infinity fibre. -/
  t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left
  /-- The morphism `T ⟶ W∞` is a closed immersion. -/
  [t_isClosedImmersion : IsClosedImmersion t]
  /-- The clopen part `T'` on which `Q` has the selected restriction behavior. -/
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
      (closedImmersionComplement i).ι)
  /-- The map `T ⟶ X` becomes an isomorphism over `X \ Z`. -/
  T_complement_isIso : IsIso
    (pullback.snd (t ≫ (BivariantClass.GysinAtInfinity.infinityToX X b).left)
      (closedImmersionComplement i).ι)
  /-- The map `T' ⟶ X` becomes an isomorphism over `X \ Z`. -/
  T'_complement_isIso : IsIso
    (pullback.snd (t' ≫ t ≫
      (BivariantClass.GysinAtInfinity.infinityToX X b).left) (closedImmersionComplement i).ι)
  /-- The restriction of `Q` to `T'` has the selected vanishing or rank-bounded behavior. -/
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
  localizedAtInfinity_spec : let center := (pullback (BivariantClass.GysinAtInfinity.infinityToX X b)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))
    let inclusion : center ⟶ BivariantClass.GysinAtInfinity.infinityFiber X b :=
      pullback.fst _ _
    let displayIso : center ≅ Over.mk
        (inclusion.left ≫ (BivariantClass.GysinAtInfinity.infinityFiber X b).hom) :=
      Over.isoMk (Iso.refl _) ((Category.id_comp _).trans inclusion.w)
    BivariantClass.IsLocalizedExtension δ
      (BivariantClass.GysinAtInfinity.infinityFiber X b) (t' ≫ t) inclusion.left (p : ℤ)
      (BivariantClass.restrict δ displayIso.inv (𝟙 _) displayIso.inv
        IsPullback.of_id_snd (p : ℤ) (infinityAmbientClass i b classes Q p mode
          infinityCenter_isPerfect infinityCenter_isDefined))
      (BivariantClass.restrict δ displayIso.inv (Over.homMk inclusion.left) (𝟙 _)
        IsPullback.of_id_fst (p : ℤ) localizedAtInfinity)

namespace ClassConstruction

/-- A deformation complex and its geometric restriction and extension laws determine
an explicit localized-class construction. -/
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
        (closedImmersionComplement i).ι))
    (T_complement_isIso : IsIso
      (pullback.snd (t ≫ (BivariantClass.GysinAtInfinity.infinityToX X b).left)
        (closedImmersionComplement i).ι))
    (T'_complement_isIso : IsIso
      (pullback.snd (t' ≫ t ≫
        (BivariantClass.GysinAtInfinity.infinityToX X b).left) (closedImmersionComplement i).ι))
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
    (localizedAtInfinity_spec : let center := (pullback (BivariantClass.GysinAtInfinity.infinityToX X b)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))
    let inclusion : center ⟶ BivariantClass.GysinAtInfinity.infinityFiber X b :=
      pullback.fst _ _
    let displayIso : center ≅ Over.mk
        (inclusion.left ≫ (BivariantClass.GysinAtInfinity.infinityFiber X b).hom) :=
      Over.isoMk (Iso.refl _) ((Category.id_comp _).trans inclusion.w)
    BivariantClass.IsLocalizedExtension δ
      (BivariantClass.GysinAtInfinity.infinityFiber X b) (t' ≫ t) inclusion.left (p : ℤ)
      (BivariantClass.restrict δ displayIso.inv (𝟙 _) displayIso.inv
        IsPullback.of_id_snd (p : ℤ) (infinityAmbientClass i b classes Q p mode
          infinityCenter_isPerfect infinityCenter_isDefined))
      (BivariantClass.restrict δ displayIso.inv (Over.homMk inclusion.left) (𝟙 _)
        IsPullback.of_id_fst (p : ℤ) localizedAtInfinity)) :
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
    BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ)  :=
  @BivariantClass.pushforwardComp S _ δ _
    (pullback (BivariantClass.GysinAtInfinity.infinityToX X construction.b)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) (Over.mk (i ≫ X.hom))
    (BivariantClass.GysinAtInfinity.infinityFiber X construction.b) X
    (@instLocallyOfFiniteTypePullbackSourceOfIsProper S _ _ _
      (@BivariantClass.GysinAtInfinity.infinityFiberLocallyOfFiniteType S _ X _
        construction.b construction.b_isProper) inferInstance inferInstance
      (BivariantClass.GysinAtInfinity.infinityToX X construction.b)
      (@BivariantClass.GysinAtInfinity.infinityToXIsProper S _ X construction.b
        construction.b_isProper)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))
    inferInstance
    (@BivariantClass.GysinAtInfinity.infinityFiberLocallyOfFiniteType S _ X _
      construction.b construction.b_isProper) inferInstance
    (pullback.snd (BivariantClass.GysinAtInfinity.infinityToX X construction.b)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))
    (by
      refine @instIsProperPullbackSnd _ _ _ _ _ ?_ _
      change IsProper
        ((BivariantClass.GysinAtInfinity.infinityInclusion X construction.b).left ≫
          (BivariantClass.GysinAtInfinity.toX X construction.b).left)
      exact MorphismProperty.comp_mem (@IsProper) _ _
        (BivariantClass.GysinAtInfinity.infinityInclusionIsProper X construction.b)
        (@BivariantClass.GysinAtInfinity.toXIsProper _ _ X construction.b
          construction.b_isProper))
    (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
    (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X construction.b)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))
    (BivariantClass.GysinAtInfinity.infinityToX X construction.b)
    pullback.condition (p : ℤ) construction.localizedAtInfinity
    (@BivariantClass.gysinAtInfinity S _ _ δ _ X _ construction.b
      construction.b_isProper construction.b_affinePart_isIso)

end ClassConstruction

namespace GlobalProducer

/-- The graph complex restricts over the affine part to the pullback of the original complex. -/
theorem affineRestriction_iso
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (mode : RestrictionBehavior) (situation : Situation S δ X i E p mode) :
    IsIsomorphic
      ((RingedSpace.modulePullbackDerived
        ((GlobalProducer.b δ X i E p mode situation) ⁻¹ᵁ BivariantClass.GysinAtInfinity.affinePart X).ι.toShHom).obj (GlobalProducer.Q δ X i E p mode situation))
      ((RingedSpace.modulePullbackDerived (affineDeformationProjection (GlobalProducer.b δ X i E p mode situation)).toShHom).obj E) := sorry

/-- The graph complex restricts on the lifted zero fibre to the original complex. -/
theorem zeroRestriction_iso
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (mode : RestrictionBehavior) (situation : Situation S δ X i E p mode) :
    IsIsomorphic
      (@zeroFiberRestriction S X _ (GlobalProducer.b δ X i E p mode situation)
        (GlobalProducer.b_affine_iso δ X i E p mode situation) (GlobalProducer.Q δ X i E p mode situation)) E := sorry

/-- The closed graph locus contains the part of the infinity fibre lying away from the center. -/
theorem containsComplement
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (mode : RestrictionBehavior) (situation : Situation S δ X i E p mode) :
    (BivariantClass.GysinAtInfinity.infinityToX X (GlobalProducer.b δ X i E p mode situation)).left.base ⁻¹' (Set.range i.base)ᶜ ⊆ Set.range (GlobalProducer.t δ X i E p mode situation).base := sorry

/-- The infinity fibre maps isomorphically to the complement of the center. -/
theorem infinityComplement_isIso
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (mode : RestrictionBehavior) (situation : Situation S δ X i E p mode) :
    IsIso (pullback.snd (BivariantClass.GysinAtInfinity.infinityToX X (GlobalProducer.b δ X i E p mode situation)).left (closedImmersionComplement i).ι) := sorry

/-- The closed graph locus maps isomorphically to the complement of the center. -/
theorem TComplement_isIso
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (mode : RestrictionBehavior) (situation : Situation S δ X i E p mode) :
    IsIso (pullback.snd ((GlobalProducer.t δ X i E p mode situation) ≫ (BivariantClass.GysinAtInfinity.infinityToX X (GlobalProducer.b δ X i E p mode situation)).left) (closedImmersionComplement i).ι) := sorry

/-- The selected clopen graph locus maps isomorphically to the complement of the center. -/
theorem TprimeComplement_isIso
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (mode : RestrictionBehavior) (situation : Situation S δ X i E p mode) :
    IsIso (pullback.snd ((GlobalProducer.tprime δ X i E p mode situation) ≫ (GlobalProducer.t δ X i E p mode situation) ≫ (BivariantClass.GysinAtInfinity.infinityToX X (GlobalProducer.b δ X i E p mode situation)).left) (closedImmersionComplement i).ι) := sorry

/-- The graph complex has the selected vanishing or rank-bound behavior on its clopen locus. -/
theorem restrictionOnTprime
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (mode : RestrictionBehavior) (situation : Situation S δ X i E p mode) :
    RestrictionCondition ((GlobalProducer.tprime δ X i E p mode situation) ≫ (GlobalProducer.t δ X i E p mode situation) ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X (GlobalProducer.b δ X i E p mode situation)).left) (GlobalProducer.Q δ X i E p mode situation) p mode := sorry

/-- The graph-localized infinity class extends the characteristic class of the restricted graph complex. -/
theorem localizedInfinity_isExtension
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (mode : RestrictionBehavior) (situation : Situation S δ X i E p mode) :
    let b := GlobalProducer.b δ X i E p mode situation
    let center := (pullback (BivariantClass.GysinAtInfinity.infinityToX X b)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))
    let inclusion : center ⟶ BivariantClass.GysinAtInfinity.infinityFiber X b :=
      pullback.fst _ _
    let displayIso : center ≅ Over.mk
        (inclusion.left ≫ (BivariantClass.GysinAtInfinity.infinityFiber X b).hom) :=
      Over.isoMk (Iso.refl _) ((Category.id_comp _).trans inclusion.w)
    @BivariantClass.IsLocalizedExtension S _ δ _
      (BivariantClass.GysinAtInfinity.infinityFiber X b) inferInstance _ _
      ((GlobalProducer.tprime δ X i E p mode situation) ≫
        (GlobalProducer.t δ X i E p mode situation)) inclusion.left
      inferInstance (GlobalProducer.center_closed δ X i E p mode situation) (p : ℤ)
      (BivariantClass.restrict δ displayIso.inv (𝟙 _) displayIso.inv
        IsPullback.of_id_snd (p : ℤ) (infinityAmbientClass i b classes (GlobalProducer.Q δ X i E p mode situation) p mode
          (GlobalProducer.centerInput_perfect δ X i E p mode situation)
          (GlobalProducer.centerInput_defined δ X i E p mode situation)))
      (BivariantClass.restrict δ displayIso.inv (Over.homMk inclusion.left) (𝟙 _)
        IsPullback.of_id_fst (p : ℤ) (GlobalProducer.localizedInfinity δ X i classes E p mode situation)) := sorry

end GlobalProducer

namespace ClassConstruction

/-- The graph deformation, its perfect complex, and its localized infinity class
form an admissible deformation construction. -/
def fromSituation
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (mode : RestrictionBehavior) (situation : Situation S δ X i E p mode) :
    ClassConstruction δ i classes E p mode situation where
  W := GlobalProducer.W δ X i E p mode situation
  b := GlobalProducer.b δ X i E p mode situation
  b_isProper := GlobalProducer.b_proper δ X i E p mode situation
  b_affinePart_isIso := GlobalProducer.b_affine_iso δ X i E p mode situation
  Q := GlobalProducer.Q δ X i E p mode situation
  Q_isPerfect := Scheme.PerfectGraphAtlas.globalQ_isPerfect E situation.perfect
    (GlobalProducer.projection X) (GlobalProducer.divisor X)
  affineDeformation_iso := GlobalProducer.affineRestriction_iso E p mode situation
  zeroFiber_iso := GlobalProducer.zeroRestriction_iso E p mode situation
  T := GlobalProducer.T δ X i E p mode situation
  t := GlobalProducer.t δ X i E p mode situation
  t_isClosedImmersion := GlobalProducer.t_closed δ X i E p mode situation
  T' := GlobalProducer.Tprime δ X i E p mode situation
  t' := GlobalProducer.tprime δ X i E p mode situation
  t'_isOpenImmersion := GlobalProducer.tprime_open δ X i E p mode situation
  t'_isClosedImmersion := GlobalProducer.tprime_closed δ X i E p mode situation
  containsComplement := GlobalProducer.containsComplement E p mode situation
  infinityFiber_complement_isIso := GlobalProducer.infinityComplement_isIso E p mode situation
  T_complement_isIso := GlobalProducer.TComplement_isIso E p mode situation
  T'_complement_isIso := GlobalProducer.TprimeComplement_isIso E p mode situation
  onT' := GlobalProducer.restrictionOnTprime E p mode situation
  infinityCenter_isPerfect := GlobalProducer.centerInput_perfect δ X i E p mode situation
  infinityCenter_isDefined := GlobalProducer.centerInput_defined δ X i E p mode situation
  infinityCenter_isClosedImmersion := GlobalProducer.center_closed δ X i E p mode situation
  localizedAtInfinity := GlobalProducer.localizedInfinity δ X i classes E p mode situation
  localizedAtInfinity_spec := GlobalProducer.localizedInfinity_isExtension classes E p mode situation

/-- A bivariant class is a construction result if it is obtained from an admissible deformation. -/
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
        localized = construction.result := Iff.rfl

end ClassConstruction

end AlgebraicGeometry.LocalizedChern
