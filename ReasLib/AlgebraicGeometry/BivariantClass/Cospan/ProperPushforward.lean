/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Cospan
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative.Reindex
public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward.Composition
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.BaseChange

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.Cospan

/-- The two composites defining the pullback of a proper morphism along an
identity-leg pullback agree. -/
theorem properBaseChangeMap_comm
    {S : Scheme.{u}} {X₁ X₂ Z' Y' : Over S} (f : X₂ ⟶ X₁) (g : Z' ⟶ X₁)
    (iY : Y' ⟶ X₂) (qY : Y' ⟶ Z')
    (squareY : IsPullback iY.left qY.left f.left g.left) :
    (iY.left ≫ f.left) ≫ (𝟙 X₁ : X₁ ⟶ X₁).left = qY.left ≫ g.left := by
  simpa using squareY.w

/-- The displayed base-change comparison respects the maps to the base scheme. -/
theorem properBaseChangeMap_over
    {S : Scheme.{u}} {X₁ X₂ Z' X' Y' : Over S} (f : X₂ ⟶ X₁) (g : Z' ⟶ X₁)
    (iX : X' ⟶ X₁) (qX : X' ⟶ Z')
    (squareX : IsPullback iX.left qX.left (𝟙 X₁ : X₁ ⟶ X₁).left g.left)
    (iY : Y' ⟶ X₂) (qY : Y' ⟶ Z')
    (squareY : IsPullback iY.left qY.left f.left g.left) :
    squareX.lift (iY.left ≫ f.left) qY.left
        (properBaseChangeMap_comm f g iY qY squareY) ≫ X'.hom = Y'.hom := by
  rw [← qX.w, ← Category.assoc, squareX.lift_snd, qY.w]

/-- The base-changed map from the pullback of `f` to a displayed pullback of the
identity of its target. -/
def properBaseChangeMap
    {S : Scheme.{u}} {X₁ X₂ Z' X' Y' : Over S} (f : X₂ ⟶ X₁) (g : Z' ⟶ X₁)
    (iX : X' ⟶ X₁) (qX : X' ⟶ Z')
    (squareX : IsPullback iX.left qX.left (𝟙 X₁ : X₁ ⟶ X₁).left g.left)
    (iY : Y' ⟶ X₂) (qY : Y' ⟶ Z')
    (squareY : IsPullback iY.left qY.left f.left g.left) : Y' ⟶ X' :=
  Over.homMk
    (squareX.lift (iY.left ≫ f.left) qY.left (properBaseChangeMap_comm f g iY qY squareY))
    (properBaseChangeMap_over f g iX qX squareX iY qY squareY)

/-- The base-changed proper map has the expected projection to the source of the
identity leg. -/
theorem properBaseChangeMap_fst
    {S : Scheme.{u}} {X₁ X₂ Z' X' Y' : Over S} (f : X₂ ⟶ X₁) (g : Z' ⟶ X₁)
    (iX : X' ⟶ X₁) (qX : X' ⟶ Z')
    (squareX : IsPullback iX.left qX.left (𝟙 X₁ : X₁ ⟶ X₁).left g.left)
    (iY : Y' ⟶ X₂) (qY : Y' ⟶ Z')
    (squareY : IsPullback iY.left qY.left f.left g.left) :
    (properBaseChangeMap f g iX qX squareX iY qY squareY).left ≫ iX.left =
      iY.left ≫ f.left := by
  exact squareX.lift_fst _ _ _

/-- The base-changed proper map has the expected projection to the varying middle
scheme. -/
theorem properBaseChangeMap_snd
    {S : Scheme.{u}} {X₁ X₂ Z' X' Y' : Over S} (f : X₂ ⟶ X₁) (g : Z' ⟶ X₁)
    (iX : X' ⟶ X₁) (qX : X' ⟶ Z')
    (squareX : IsPullback iX.left qX.left (𝟙 X₁ : X₁ ⟶ X₁).left g.left)
    (iY : Y' ⟶ X₂) (qY : Y' ⟶ Z')
    (squareY : IsPullback iY.left qY.left f.left g.left) :
    (properBaseChangeMap f g iX qX squareX iY qY squareY).left ≫ qX.left = qY.left := by
  exact squareX.lift_snd _ _ _

/-- A further base change of the middle scheme gives a cartesian square of the
displayed comparison maps. -/
private theorem properBaseChangeMap_innerSquare
    {S : Scheme.{u}} {X₁ X₂ Z' X' Y' Z'' X'' Y'' : Over S}
    (f : X₂ ⟶ X₁) (g : Z' ⟶ X₁) (iX : X' ⟶ X₁) (qX : X' ⟶ Z')
    (squareX : IsPullback iX.left qX.left (𝟙 X₁ : X₁ ⟶ X₁).left g.left)
    (iY : Y' ⟶ X₂) (qY : Y' ⟶ Z')
    (squareY : IsPullback iY.left qY.left f.left g.left)
    (h : Z'' ⟶ Z') (jX : X'' ⟶ X') (qX' : X'' ⟶ Z'')
    (innerX : IsPullback jX.left qX'.left qX.left h.left)
    (jY : Y'' ⟶ Y') (qY' : Y'' ⟶ Z'')
    (innerY : IsPullback jY.left qY'.left qY.left h.left) :
    IsPullback jY.left
      (properBaseChangeMap f (h ≫ g) (jX ≫ iX) qX' (innerX.paste_horiz squareX)
        (jY ≫ iY) qY' (innerY.paste_horiz squareY)).left
      (properBaseChangeMap f g iX qX squareX iY qY squareY).left jX.left := by
  have w : jY.left ≫ (properBaseChangeMap f g iX qX squareX iY qY squareY).left =
      (properBaseChangeMap f (h ≫ g) (jX ≫ iX) qX' (innerX.paste_horiz squareX)
        (jY ≫ iY) qY' (innerY.paste_horiz squareY)).left ≫ jX.left := by
    apply squareX.hom_ext
    · simp [properBaseChangeMap, Category.assoc]
    · calc
        (jY.left ≫ (properBaseChangeMap f g iX qX squareX iY qY squareY).left) ≫
            qX.left = jY.left ≫ qY.left := by
          rw [Category.assoc, properBaseChangeMap_snd]
        _ = qY'.left ≫ h.left := innerY.w
        _ = ((properBaseChangeMap f (h ≫ g) (jX ≫ iX) qX'
            (innerX.paste_horiz squareX) (jY ≫ iY) qY'
            (innerY.paste_horiz squareY)).left ≫ jX.left) ≫ qX.left := by
          rw [Category.assoc, innerX.w, ← Category.assoc, properBaseChangeMap_snd]
  apply IsPullback.of_bot _ w innerX
  simpa only [properBaseChangeMap_snd] using innerY

/-- A displayed base change of a proper morphism along an identity-leg pullback is
proper. -/
instance properBaseChangeMapIsProper
    {S : Scheme.{u}} {X₁ X₂ Z' X' Y' : Over S} (f : X₂ ⟶ X₁) [IsProper f.left]
    (g : Z' ⟶ X₁) (iX : X' ⟶ X₁) (qX : X' ⟶ Z')
    (squareX : IsPullback iX.left qX.left (𝟙 X₁ : X₁ ⟶ X₁).left g.left)
    (iY : Y' ⟶ X₂) (qY : Y' ⟶ Z')
    (squareY : IsPullback iY.left qY.left f.left g.left) :
    IsProper (properBaseChangeMap f g iX qX squareX iY qY squareY).left := by
  haveI : IsIso qX.left := squareX.isIso_snd_of_isIso
  haveI : IsProper qY.left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback squareY inferInstance
  haveI : IsProper
      ((properBaseChangeMap f g iX qX squareX iY qY squareY).left ≫ qX.left) := by
    rw [properBaseChangeMap_snd]
    infer_instance
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsProper) _ qX.left).mp
    inferInstance

/-- The cap family given by proper pushforward along the displayed base change of a
proper morphism. -/
def properPushforwardCap
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X₁ X₂ : Over S} [LocallyOfFiniteType X₁.hom] [LocallyOfFiniteType X₂.hom]
    (f : X₂ ⟶ X₁) [IsProper f.left] : CapFamily delta (𝟙 X₁) f 0 :=
  fun {_ X' Y'} _ _ _ g _ iX qX squareX iY _ qY squareY k ↦
    (RelativeChow.castDegree delta (Int.sub_zero k).symm).comp
      (ChowGroup.map delta Y' X'
        (properBaseChangeMap f g iX qX squareX iY qY squareY) k)

/-- Evaluation of the proper-pushforward cap family is Chow pushforward along the
displayed base-change map, followed by the degree-zero transport. -/
theorem properPushforwardCap_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X₁ X₂ Z' X' Y' : Over S}
    [LocallyOfFiniteType X₁.hom] [LocallyOfFiniteType X₂.hom]
    [LocallyOfFiniteType Z'.hom] [LocallyOfFiniteType X'.hom]
    [LocallyOfFiniteType Y'.hom]
    (f : X₂ ⟶ X₁) [IsProper f.left] (g : Z' ⟶ X₁) [LocallyOfFiniteType g.left]
    (iX : X' ⟶ X₁) (qX : X' ⟶ Z')
    (squareX : IsPullback iX.left qX.left (𝟙 X₁ : X₁ ⟶ X₁).left g.left)
    (iY : Y' ⟶ X₂) [LocallyOfFiniteType iY.left] (qY : Y' ⟶ Z')
    (squareY : IsPullback iY.left qY.left f.left g.left) (k : ℤ) :
    properPushforwardCap delta f g iX qX squareX iY qY squareY k =
      (RelativeChow.castDegree delta (Int.sub_zero k).symm).comp
        (ChowGroup.map delta Y' X'
          (properBaseChangeMap f g iX qX squareX iY qY squareY) k) := by
  rfl

/-- Proper pushforward cap maps satisfy proper-pushforward compatibility. -/
theorem properPushforwardCap_mapProper
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X₁ X₂ : Over S} [LocallyOfFiniteType X₁.hom] [LocallyOfFiniteType X₂.hom]
    (f : X₂ ⟶ X₁) [IsProper f.left] :
    CompatibleWithProperPushforward delta (properPushforwardCap delta f) := by
  intro Z' X' Y' Z'' X'' Y'' _ _ _ _ _ _ g _ iX qX squareX iY _ qY squareY
    h jX qX' innerX jY qY' innerY _ _ _ k alpha
  let F := properBaseChangeMap f g iX qX squareX iY qY squareY
  let F' := properBaseChangeMap f (h ≫ g) (jX ≫ iX) qX'
    (innerX.paste_horiz squareX) (jY ≫ iY) qY' (innerY.paste_horiz squareY)
  have comm : jY ≫ F = F' ≫ jX := by
    apply Over.OverMorphism.ext
    exact (properBaseChangeMap_innerSquare f g iX qX squareX iY qY squareY
      h jX qX' innerX jY qY' innerY).w
  have maps : ChowGroup.map delta Y' X' F k (ChowGroup.map delta Y'' Y' jY k alpha) =
      ChowGroup.map delta X'' X' jX k (ChowGroup.map delta Y'' X'' F' k alpha) := by
    change ((ChowGroup.map delta Y' X' F k).comp
        (ChowGroup.map delta Y'' Y' jY k)) alpha =
      ((ChowGroup.map delta X'' X' jX k).comp
        (ChowGroup.map delta Y'' X'' F' k)) alpha
    rw [ChowGroup.map_comp, ChowGroup.map_comp]
    simp only [comm]
  have transport (n : ℤ) (e : k = n) :
      RelativeChow.castDegree delta e
        (ChowGroup.map delta Y' X' F k (ChowGroup.map delta Y'' Y' jY k alpha)) =
      ChowGroup.map delta X'' X' jX n
        (RelativeChow.castDegree delta e (ChowGroup.map delta Y'' X'' F' k alpha)) := by
    cases e
    exact maps
  exact transport (k - 0) (Int.sub_zero k).symm

/-- Proper pushforward cap maps satisfy fixed-relative-dimension flat-pullback
compatibility. -/
theorem properPushforwardCap_pullbackFlat
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X₁ X₂ : Over S} [LocallyOfFiniteType X₁.hom] [LocallyOfFiniteType X₂.hom]
    (f : X₂ ⟶ X₁) [IsProper f.left] :
    CompatibleWithFlatPullback delta (properPushforwardCap delta f) := by
  intro Z' X' Y' Z'' X'' Y'' _ _ _ _ _ _ g _ iX qX squareX iY _ qY squareY
    h jX qX' innerX jY qY' innerY d _ _ _ _ _ _ k alpha
  let F := properBaseChangeMap f g iX qX squareX iY qY squareY
  let F' := properBaseChangeMap f (h ≫ g) (jX ≫ iX) qX'
    (innerX.paste_horiz squareX) (jY ≫ iY) qY' (innerY.paste_horiz squareY)
  have square : IsPullback jY.left F'.left F.left jX.left :=
    properBaseChangeMap_innerSquare f g iX qX squareX iY qY squareY
      h jX qX' innerX jY qY' innerY
  have maps : ChowGroup.map delta Y'' X'' F' (k + d)
      (ChowGroup.flatPullback delta Y'' Y' jY d k alpha) =
      ChowGroup.flatPullback delta X'' X' jX d k (ChowGroup.map delta Y' X' F k alpha) := by
    letI : IsLocallyNoetherian X''.left := LocallyOfFiniteType.isLocallyNoetherian X''.hom
    refine Quotient.inductionOn' alpha ?_
    intro a
    change chowClass _ (k + d)
        (CycleGroup.mapHom F'.left _ _ (k + d) (CycleGroup.flatPullback delta Y'' Y' jY d k a)) =
      chowClass _ (k + d)
        (CycleGroup.flatPullback delta X'' X' jX d k (CycleGroup.mapHom F.left _ _ k a))
    exact congrArg (chowClass (X''.hom.relativeDimensionFunction delta) (k + (d : ℤ)))
      (CycleGroup.flatPullback_map_of_isPullback delta Y' X' Y'' X''
        jY F' F jX square d k a).symm
  have transport (n m : ℤ) (e : k = n) (e' : k + (d : ℤ) = m) :
      HEq (RelativeChow.castDegree delta e'
        (ChowGroup.map delta Y'' X'' F' (k + d)
          (ChowGroup.flatPullback delta Y'' Y' jY d k alpha)))
        (ChowGroup.flatPullback delta X'' X' jX d n
          (RelativeChow.castDegree delta e (ChowGroup.map delta Y' X' F k alpha))) := by
    cases e
    cases e'
    exact heq_of_eq maps
  exact transport (k - 0) (k + d - 0)
    (Int.sub_zero k).symm (Int.sub_zero (k + d)).symm

/-- Proper pushforward cap maps satisfy effective-Cartier Gysin compatibility. -/
theorem properPushforwardCap_gysinCartier
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X₁ X₂ : Over S} [LocallyOfFiniteType X₁.hom] [LocallyOfFiniteType X₂.hom]
    (f : X₂ ⟶ X₁) [IsProper f.left] :
    CompatibleWithCartierGysin delta (properPushforwardCap delta f) := sorry

/-- A proper morphism `f : X₂ ⟶ X₁` defines a degree-zero bivariant cospan
operation on `X₁ ⟶ X₁ ⟵ X₂` by proper pushforward after every base change. -/
def properPushforward
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X₁ X₂ : Over S} [LocallyOfFiniteType X₁.hom] [LocallyOfFiniteType X₂.hom]
    (f : X₂ ⟶ X₁) [IsProper f.left] : Cospan delta (𝟙 X₁) f 0 where
  cap := properPushforwardCap delta f
  map_proper := properPushforwardCap_mapProper delta f
  pullback_flat := properPushforwardCap_pullbackFlat delta f
  gysin_cartier := properPushforwardCap_gysinCartier delta f

/-- Evaluation of the proper cospan class is Chow pushforward along the displayed
base-change map. -/
theorem properPushforward_cap
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X₁ X₂ Z' X' Y' : Over S}
    [LocallyOfFiniteType X₁.hom] [LocallyOfFiniteType X₂.hom]
    [LocallyOfFiniteType Z'.hom] [LocallyOfFiniteType X'.hom]
    [LocallyOfFiniteType Y'.hom]
    (f : X₂ ⟶ X₁) [IsProper f.left] (g : Z' ⟶ X₁) [LocallyOfFiniteType g.left]
    (iX : X' ⟶ X₁) (qX : X' ⟶ Z')
    (squareX : IsPullback iX.left qX.left (𝟙 X₁ : X₁ ⟶ X₁).left g.left)
    (iY : Y' ⟶ X₂) [LocallyOfFiniteType iY.left] (qY : Y' ⟶ Z')
    (squareY : IsPullback iY.left qY.left f.left g.left) (k : ℤ) :
    (properPushforward delta f).cap g iX qX squareX iY qY squareY k =
      (RelativeChow.castDegree delta (Int.sub_zero k).symm).comp
        (ChowGroup.map delta Y' X'
          (properBaseChangeMap f g iX qX squareX iY qY squareY) k) := by
  rfl

end AlgebraicGeometry.BivariantClass.Cospan
