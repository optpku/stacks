/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper.Over

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- Pasting the base-change square of `f` with a cartesian square for `g` gives the
cartesian square used to evaluate a bivariant class on `f ≫ g`. -/
theorem properPushforwardSquare
    {S : Scheme.{u}} {X Y T Y' T' : Over S}
    (f : X ⟶ Y) (g : Y ⟶ T) (i : Y' ⟶ Y) (g' : Y' ⟶ T') (h : T' ⟶ T)
    (square : IsPullback i.left g'.left g.left h.left) :
    IsPullback (pullback.fst f i).left (pullback.snd f i ≫ g').left
      (f ≫ g).left h.left := sorry

/-- The cap family obtained by evaluating on the base change of a proper morphism and
then applying proper pushforward on relative Chow groups. -/
def properPushforwardCap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y T : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType T.hom] (f : X ⟶ Y) [IsProper f.left] (g : Y ⟶ T)
    (p : ℤ) (c : BivariantClass δ (f ≫ g) p) : CapFamily δ g p :=
  fun {Y'} {_} _ _ i g' h _ square k ↦
    (ChowGroup.map δ (pullback f i) Y' (pullback.snd f i) (k - p)).comp
      (c.cap (pullback.fst f i) (pullback.snd f i ≫ g') h
        (properPushforwardSquare f g i g' h square) k)

/-- The proper-pushforward cap family remains compatible with proper pushforward. -/
theorem properPushforwardCap_mapProper
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y T : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType T.hom] (f : X ⟶ Y) [IsProper f.left] (g : Y ⟶ T)
    (p : ℤ) (c : BivariantClass δ (f ≫ g) p) :
    CompatibleWithProperPushforward δ (properPushforwardCap δ f g p c) := sorry

/-- The proper-pushforward cap family remains compatible with flat pullback. -/
theorem properPushforwardCap_pullbackFlat
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y T : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType T.hom] (f : X ⟶ Y) [IsProper f.left] (g : Y ⟶ T)
    (p : ℤ) (c : BivariantClass δ (f ≫ g) p) :
    CompatibleWithFlatPullback δ (properPushforwardCap δ f g p c) := sorry

/-- The proper-pushforward cap family remains compatible with effective-Cartier Gysin
pullback. -/
theorem properPushforwardCap_gysinCartier
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y T : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType T.hom] (f : X ⟶ Y) [IsProper f.left] (g : Y ⟶ T)
    (p : ℤ) (c : BivariantClass δ (f ≫ g) p) :
    CompatibleWithCartierGysin δ (properPushforwardCap δ f g p c) := sorry

/-- Proper pushforward of a degree-`p` bivariant class along the first morphism in a
composable pair. -/
def properPushforward
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y T : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType T.hom] (f : X ⟶ Y) [IsProper f.left] (g : Y ⟶ T)
    (p : ℤ) (c : BivariantClass δ (f ≫ g) p) : BivariantClass δ g p where
  cap := properPushforwardCap δ f g p c
  map_proper := properPushforwardCap_mapProper δ f g p c
  pullback_flat := properPushforwardCap_pullbackFlat δ f g p c
  gysin_cartier := properPushforwardCap_gysinCartier δ f g p c

/-- Evaluation of proper pushforward is the original cap map followed by Chow
pushforward along the base-changed proper morphism. -/
theorem properPushforward_cap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y T Y' T' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType T.hom] [LocallyOfFiniteType Y'.hom]
    [LocallyOfFiniteType T'.hom] (f : X ⟶ Y) [IsProper f.left] (g : Y ⟶ T)
    (p : ℤ) (c : BivariantClass δ (f ≫ g) p)
    (i : Y' ⟶ Y) (g' : Y' ⟶ T') (h : T' ⟶ T) [LocallyOfFiniteType h.left]
    (square : IsPullback i.left g'.left g.left h.left) (k : ℤ) :
    (properPushforward δ f g p c).cap i g' h square k =
      (ChowGroup.map δ (pullback f i) Y' (pullback.snd f i) (k - p)).comp
        (c.cap (pullback.fst f i) (pullback.snd f i ≫ g') h
          (properPushforwardSquare f g i g' h square) k) := sorry

/-- Proper pushforward to the identity bivariant class on the target, with the
identity-composition transport made explicit in the input. -/
def properPushforwardToTarget
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left] (p : ℤ) (c : BivariantClass δ f p) :
    BivariantClass δ (𝟙 Y) p :=
  properPushforward δ f (𝟙 Y) p ((Category.comp_id f).symm ▸ c)

/-- Evaluation of target proper pushforward is evaluation of proper pushforward
along the identity of the target after identity-composition transport. -/
theorem properPushforwardToTarget_cap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y Y' T' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Y'.hom] [LocallyOfFiniteType T'.hom]
    (f : X ⟶ Y) [IsProper f.left] (p : ℤ) (c : BivariantClass δ f p)
    (i : Y' ⟶ Y) (g' : Y' ⟶ T') (h : T' ⟶ Y) [LocallyOfFiniteType h.left]
    (square : IsPullback i.left g'.left (𝟙 Y : Y ⟶ Y).left h.left) (k : ℤ) :
    (properPushforwardToTarget δ f p c).cap i g' h square k =
      (properPushforward δ f (𝟙 Y) p ((Category.comp_id f).symm ▸ c)).cap
        i g' h square k := sorry

end AlgebraicGeometry.BivariantClass
