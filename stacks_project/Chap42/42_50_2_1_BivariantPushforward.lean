/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap42.Remark_42_33_5_Bivariant

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- An `Over S` morphism built from a proper scheme morphism is proper on its underlying map. -/
instance overHomMkProper
    {S : Scheme.{u}} {X : Over S} {Z : Scheme.{u}} (i : Z ⟶ X.left) [IsProper i] :
    IsProper (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X).left := sorry

/-- The source of a base change of a proper morphism between schemes locally of finite
type over `S` is again locally of finite type over `S`. -/
instance pullbackSourceLocallyOfFiniteType
    {S : Scheme.{u}} {X Y Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Y'.hom] (f : X ⟶ Y) [IsProper f.left] (i : Y' ⟶ Y) :
    LocallyOfFiniteType (pullback f i).hom := sorry

/-- The second projection of a base change of a proper morphism in `Over S` is proper. -/
instance pullbackSndProper
    {S : Scheme.{u}} {X Y Y' : Over S} (f : X ⟶ Y) [IsProper f.left] (i : Y' ⟶ Y) :
    IsProper (pullback.snd f i).left := sorry

/-- Pasting the base-change square of `f` with a cartesian square for `g` gives the
cartesian square used to evaluate a bivariant class on `f ≫ g`. -/
theorem pushforwardSquare
    {S : Scheme.{u}} {X Y T Y' T' : Over S}
    (f : X ⟶ Y) (g : Y ⟶ T) (i : Y' ⟶ Y) (g' : Y' ⟶ T') (h : T' ⟶ T)
    (square : IsPullback i.left g'.left g.left h.left) :
    IsPullback (pullback.fst f i).left (pullback.snd f i ≫ g').left
      (f ≫ g).left h.left := sorry

/-- The cap family obtained by evaluating on the base change of a proper morphism and
then applying proper pushforward on relative Chow groups. -/
def pushforwardCap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y T : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType T.hom] (f : X ⟶ Y) [IsProper f.left] (g : Y ⟶ T)
    (p : ℤ) (c : BivariantClass δ (f ≫ g) p) : CapFamily δ g p :=
  fun {Y'} {_} _ _ i g' h _ square k ↦
    (ChowGroup.map δ (pullback f i) Y' (pullback.snd f i) (k - p)).comp
      (c.cap (pullback.fst f i) (pullback.snd f i ≫ g') h
        (pushforwardSquare f g i g' h square) k)

/-- The proper-pushforward cap family remains compatible with proper pushforward. -/
theorem pushforwardCap_mapProper
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y T : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType T.hom] (f : X ⟶ Y) [IsProper f.left] (g : Y ⟶ T)
    (p : ℤ) (c : BivariantClass δ (f ≫ g) p) :
    CompatibleWithProperPushforward δ (pushforwardCap δ f g p c) := sorry

/-- The proper-pushforward cap family remains compatible with flat pullback. -/
theorem pushforwardCap_pullbackFlat
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y T : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType T.hom] (f : X ⟶ Y) [IsProper f.left] (g : Y ⟶ T)
    (p : ℤ) (c : BivariantClass δ (f ≫ g) p) :
    CompatibleWithFlatPullback δ (pushforwardCap δ f g p c) := sorry

/-- The proper-pushforward cap family remains compatible with effective-Cartier Gysin
pullback. -/
theorem pushforwardCap_gysinCartier
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y T : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType T.hom] (f : X ⟶ Y) [IsProper f.left] (g : Y ⟶ T)
    (p : ℤ) (c : BivariantClass δ (f ≫ g) p) :
    CompatibleWithCartierGysin δ (pushforwardCap δ f g p c) := sorry

/-- Proper pushforward of a degree-`p` bivariant class along the first morphism in a
composable pair. -/
def pushforward
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y T : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType T.hom] (f : X ⟶ Y) [IsProper f.left] (g : Y ⟶ T)
    (p : ℤ) (c : BivariantClass δ (f ≫ g) p) : BivariantClass δ g p where
  cap := pushforwardCap δ f g p c
  map_proper := pushforwardCap_mapProper δ f g p c
  pullback_flat := pushforwardCap_pullbackFlat δ f g p c
  gysin_cartier := pushforwardCap_gysinCartier δ f g p c

/-- Evaluation of proper pushforward is the original cap map followed by Chow
pushforward along the base-changed proper morphism. -/
theorem pushforward_cap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y T Y' T' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType T.hom] [LocallyOfFiniteType Y'.hom]
    [LocallyOfFiniteType T'.hom] (f : X ⟶ Y) [IsProper f.left] (g : Y ⟶ T)
    (p : ℤ) (c : BivariantClass δ (f ≫ g) p)
    (i : Y' ⟶ Y) (g' : Y' ⟶ T') (h : T' ⟶ T) [LocallyOfFiniteType h.left]
    (square : IsPullback i.left g'.left g.left h.left) (k : ℤ) :
    (pushforward δ f g p c).cap i g' h square k =
      (ChowGroup.map δ (pullback f i) Y' (pullback.snd f i) (k - p)).comp
        (c.cap (pullback.fst f i) (pullback.snd f i ≫ g') h
          (pushforwardSquare f g i g' h square) k) := sorry

/-- Proper pushforward to the target, with the identity-composition transport hidden from
the resulting bivariant class. -/
def pushforwardToTarget
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left] (p : ℤ) (c : BivariantClass δ f p) :
    BivariantClass δ (𝟙 Y) p :=
  pushforward δ f (𝟙 Y) p ((Category.comp_id f).symm ▸ c)

/-- Evaluation of target pushforward is evaluation of generic proper pushforward after
the canonical identity-composition transport. -/
theorem pushforwardToTarget_cap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y Y' T' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Y'.hom] [LocallyOfFiniteType T'.hom]
    (f : X ⟶ Y) [IsProper f.left] (p : ℤ) (c : BivariantClass δ f p)
    (i : Y' ⟶ Y) (g' : Y' ⟶ T') (h : T' ⟶ Y) [LocallyOfFiniteType h.left]
    (square : IsPullback i.left g'.left (𝟙 Y : Y ⟶ Y).left h.left) (k : ℤ) :
    (pushforwardToTarget δ f p c).cap i g' h square k =
      (pushforward δ f (𝟙 Y) p ((Category.comp_id f).symm ▸ c)).cap
        i g' h square k := sorry

end AlgebraicGeometry.BivariantClass
