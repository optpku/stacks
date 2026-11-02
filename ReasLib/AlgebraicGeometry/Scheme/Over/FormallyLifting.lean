/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

/-!
# Formally smooth, étale, and unramified functor transformations

A natural transformation of functors on schemes over a base is formally smooth,
formally étale, or formally unramified according as every solid commutative square
against an affine first-order thickening admits a dotted lift, a unique dotted lift,
or at most one dotted lift.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Over

/-- Restriction along an over-morphism paired with the component of a transformation
at the thickened object. -/
def liftPair {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G)
    {T T' : Over S} (i : T ⟶ T') :
    F.obj (op T') → F.obj (op T) × G.obj (op T') :=
  fun x' ↦ (F.map (op i) x', a.app (op T') x')

/-- `liftPair a i x'` is the pair `(F.map (op i) x', a.app (op T') x')`. -/
theorem liftPair_apply {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G)
    {T T' : Over S} (i : T ⟶ T') (x' : F.obj (op T')) :
    liftPair a i x' = (F.map (op i) x', a.app (op T') x') := rfl

/-- The first factor of `liftPair a i x'` is restriction of `x'` along `i`. -/
theorem liftPair_fst {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G)
    {T T' : Over S} (i : T ⟶ T') (x' : F.obj (op T')) :
    (liftPair a i x').1 = F.map (op i) x' := rfl

/-- The second factor of `liftPair a i x'` is the image of `x'` under `a` at `T'`. -/
theorem liftPair_snd {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G)
    {T T' : Over S} (i : T ⟶ T') (x' : F.obj (op T')) :
    (liftPair a i x').2 = a.app (op T') x' := rfl

/-- A transformation of functors on schemes over `S` is formally smooth when every
solid commutative square against an affine first-order thickening admits a dotted
lift. -/
class FormallySmooth {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G) : Prop where
  /-- Every compatible pair of sections against an affine first-order thickening lifts. -/
  exists_lift : ∀ {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (i : T ⟶ T')
    [IsFirstOrderThickening i.left] (x : F.obj (op T)) (y : G.obj (op T')),
    a.app (op T) x = G.map (op i) y → ∃ x' : F.obj (op T'), liftPair a i x' = (x, y)

/-- A transformation of functors on schemes over `S` is formally étale when every
solid commutative square against an affine first-order thickening admits a unique
dotted lift. -/
class FormallyEtale {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G) : Prop where
  /-- Every compatible pair of sections against an affine first-order thickening lifts uniquely. -/
  unique_lift : ∀ {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (i : T ⟶ T')
    [IsFirstOrderThickening i.left] (x : F.obj (op T)) (y : G.obj (op T')),
    a.app (op T) x = G.map (op i) y → ∃! x' : F.obj (op T'), liftPair a i x' = (x, y)

/-- A transformation of functors on schemes over `S` is formally unramified when every
solid commutative square against an affine first-order thickening admits at most one
dotted lift. -/
class FormallyUnramified {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G) : Prop where
  /-- The pairing map along every affine first-order thickening is injective. -/
  injective_lift : ∀ {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (i : T ⟶ T')
    [IsFirstOrderThickening i.left], Function.Injective (liftPair a i)

/-- Formal smoothness is the existence of a dotted lift against every affine first-order
thickening. -/
theorem formallySmooth_iff {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G) :
    FormallySmooth a ↔
      ∀ {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (i : T ⟶ T')
        [IsFirstOrderThickening i.left] (x : F.obj (op T)) (y : G.obj (op T')),
        a.app (op T) x = G.map (op i) y → ∃ x' : F.obj (op T'), liftPair a i x' = (x, y) :=
  ⟨fun h => h.exists_lift, fun h => ⟨h⟩⟩

/-- Formal étaleness is the existence of a unique dotted lift against every affine
first-order thickening. -/
theorem formallyEtale_iff {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G) :
    FormallyEtale a ↔
      ∀ {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (i : T ⟶ T')
        [IsFirstOrderThickening i.left] (x : F.obj (op T)) (y : G.obj (op T')),
        a.app (op T) x = G.map (op i) y → ∃! x' : F.obj (op T'), liftPair a i x' = (x, y) :=
  ⟨fun h => h.unique_lift, fun h => ⟨h⟩⟩

/-- Formal unramifiedness is injectivity of `liftPair` along every affine first-order
thickening. -/
theorem formallyUnramified_iff {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G) :
    FormallyUnramified a ↔
      ∀ {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (i : T ⟶ T')
        [IsFirstOrderThickening i.left], Function.Injective (liftPair a i) :=
  ⟨fun h => h.injective_lift, fun h => ⟨h⟩⟩

namespace FormallySmooth

/-- The identity transformation is formally smooth. -/
instance id {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type v) : FormallySmooth (𝟙 F) where
  exists_lift := by
    intro T T' _ _ i _ x y h
    exact ⟨y, Prod.ext h.symm rfl⟩

/-- A formally smooth transformation has the right lifting property against the Yoneda
image of every affine first-order thickening. -/
instance hasLiftingProperty {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    {a : F ⟶ G} [FormallySmooth a] {T T' : Over S} [IsAffine T.left] [IsAffine T'.left]
    (i : T ⟶ T') [IsFirstOrderThickening i.left] :
    HasLiftingProperty (yoneda.map i) a := by
  constructor
  intro f g sq
  have hc : a.app (op T) (yonedaEquiv f) = G.map (op i) (yonedaEquiv g) := by
    calc
      _ = yonedaEquiv (f ≫ a) := (yonedaEquiv_comp f a).symm
      _ = yonedaEquiv (yoneda.map i ≫ g) := congrArg yonedaEquiv sq.w
      _ = _ := (yonedaEquiv_naturality g i).symm
  obtain ⟨z, hz⟩ := FormallySmooth.exists_lift i (yonedaEquiv f) (yonedaEquiv g) hc
  have hleft := congrArg Prod.fst hz
  have hright := congrArg Prod.snd hz
  refine CommSq.HasLift.mk' ⟨yonedaEquiv.symm z, ?_, ?_⟩
  · apply yonedaEquiv.injective
    calc
      _ = F.map (op i) (yonedaEquiv (yonedaEquiv.symm z)) :=
        (yonedaEquiv_naturality _ i).symm
      _ = _ := by simpa [liftPair] using hleft
  · apply yonedaEquiv.injective
    calc
      _ = a.app (op T') (yonedaEquiv (yonedaEquiv.symm z)) := yonedaEquiv_comp _ a
      _ = _ := by simpa [liftPair] using hright

end FormallySmooth

namespace FormallyEtale

/-- The identity transformation is formally étale. -/
instance id {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type v) : FormallyEtale (𝟙 F) where
  unique_lift := by
    intro T T' _ _ i _ x y h
    exact ⟨y, Prod.ext h.symm rfl, fun z hz => congrArg Prod.snd hz⟩

/-- A formally étale transformation is formally smooth. -/
instance (priority := 100) toFormallySmooth {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v}
    {a : F ⟶ G} [FormallyEtale a] : FormallySmooth a where
  exists_lift := by
    intro T T' _ _ i _ x y h
    exact (FormallyEtale.unique_lift i x y h).exists

/-- A formally étale transformation is formally unramified. -/
instance (priority := 100) toFormallyUnramified {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v}
    {a : F ⟶ G} [FormallyEtale a] : FormallyUnramified a where
  injective_lift := by
    intro T T' _ _ i _ x y h
    have hc : a.app (op T) (F.map (op i) x) = G.map (op i) (a.app (op T') x) := by
      simpa using NatTrans.naturality_apply a (op i) x
    obtain ⟨z, hz, hu⟩ := FormallyEtale.unique_lift i (F.map (op i) x) (a.app (op T') x) hc
    exact (hu x rfl).trans (hu y h.symm).symm

/-- Formal étaleness is equivalent to being both formally smooth and formally unramified. -/
theorem iff_formallySmooth_and_formallyUnramified {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G) :
    FormallyEtale a ↔ FormallySmooth a ∧ FormallyUnramified a := by
  constructor
  · intro h
    letI : FormallyEtale a := h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hs, hu⟩
    letI : FormallySmooth a := hs
    letI : FormallyUnramified a := hu
    constructor
    intro T T' _ _ i _ x y h
    obtain ⟨z, hz⟩ := FormallySmooth.exists_lift i x y h
    exact ⟨z, hz, fun z' hz' => FormallyUnramified.injective_lift i (hz'.trans hz.symm)⟩

/-- A formally étale transformation has a unique Yoneda lift through every affine
first-order thickening. -/
theorem existsUnique_liftStruct {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    {a : F ⟶ G} [FormallyEtale a] {T T' : Over S} [IsAffine T.left] [IsAffine T'.left]
    (i : T ⟶ T') [IsFirstOrderThickening i.left] {f : yoneda.obj T ⟶ F}
    {g : yoneda.obj T' ⟶ G} (sq : CommSq f (yoneda.map i) a g) :
    Nonempty (Unique sq.LiftStruct) := by
  obtain ⟨l⟩ := (HasLiftingProperty.sq_hasLift sq).exists_lift
  refine ⟨{ default := l, uniq := ?_ }⟩
  intro r
  apply CommSq.LiftStruct.ext
  apply yonedaEquiv.injective
  apply FormallyUnramified.injective_lift (a := a) i
  apply Prod.ext
  · change F.map (op i) (yonedaEquiv r.l) = F.map (op i) (yonedaEquiv l.l)
    calc
      _ = yonedaEquiv (yoneda.map i ≫ r.l) := yonedaEquiv_naturality r.l i
      _ = yonedaEquiv (yoneda.map i ≫ l.l) := by rw [r.fac_left, l.fac_left]
      _ = _ := (yonedaEquiv_naturality l.l i).symm
  · change a.app (op T') (yonedaEquiv r.l) = a.app (op T') (yonedaEquiv l.l)
    rw [← yonedaEquiv_comp, ← yonedaEquiv_comp, r.fac_right, l.fac_right]

end FormallyEtale

namespace FormallyUnramified

/-- The identity transformation is formally unramified. -/
instance id {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type v) : FormallyUnramified (𝟙 F) where
  injective_lift := by
    intro T T' _ _ i _ x y h
    exact congrArg Prod.snd h

/-- Sections of a formally unramified transformation that restrict equally along an
affine first-order thickening and have the same image under `a` are equal. -/
theorem hom_ext {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} {a : F ⟶ G}
    [FormallyUnramified a] {T T' : Over S} [IsAffine T.left] [IsAffine T'.left]
    (i : T ⟶ T') [IsFirstOrderThickening i.left] {x₁ x₂ : F.obj (op T')}
    (h : liftPair a i x₁ = liftPair a i x₂) : x₁ = x₂ :=
  FormallyUnramified.injective_lift i h

/-- Yoneda lifts of a formally unramified transformation through an affine first-order
thickening are unique whenever they exist. -/
instance subsingleton_liftStruct {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    {a : F ⟶ G} [FormallyUnramified a] {T T' : Over S} [IsAffine T.left] [IsAffine T'.left]
    (i : T ⟶ T') [IsFirstOrderThickening i.left] {f : yoneda.obj T ⟶ F}
    {g : yoneda.obj T' ⟶ G} (sq : CommSq f (yoneda.map i) a g) :
    Subsingleton sq.LiftStruct := by
  constructor
  intro l r
  apply CommSq.LiftStruct.ext
  apply yonedaEquiv.injective
  apply FormallyUnramified.injective_lift (a := a) i
  apply Prod.ext
  · change F.map (op i) (yonedaEquiv l.l) = F.map (op i) (yonedaEquiv r.l)
    calc
      _ = yonedaEquiv (yoneda.map i ≫ l.l) := yonedaEquiv_naturality l.l i
      _ = yonedaEquiv (yoneda.map i ≫ r.l) := by rw [l.fac_left, r.fac_left]
      _ = _ := (yonedaEquiv_naturality r.l i).symm
  · change a.app (op T') (yonedaEquiv l.l) = a.app (op T') (yonedaEquiv r.l)
    rw [← yonedaEquiv_comp, ← yonedaEquiv_comp, l.fac_right, r.fac_right]

end FormallyUnramified

end AlgebraicGeometry.Scheme.Over
