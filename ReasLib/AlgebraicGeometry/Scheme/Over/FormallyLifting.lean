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
    liftPair a i x' = (F.map (op i) x', a.app (op T') x') := sorry

/-- The first factor of `liftPair a i x'` is restriction of `x'` along `i`. -/
theorem liftPair_fst {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G)
    {T T' : Over S} (i : T ⟶ T') (x' : F.obj (op T')) :
    (liftPair a i x').1 = F.map (op i) x' := sorry

/-- The second factor of `liftPair a i x'` is the image of `x'` under `a` at `T'`. -/
theorem liftPair_snd {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G)
    {T T' : Over S} (i : T ⟶ T') (x' : F.obj (op T')) :
    (liftPair a i x').2 = a.app (op T') x' := sorry

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
        a.app (op T) x = G.map (op i) y → ∃ x' : F.obj (op T'), liftPair a i x' = (x, y) := sorry

/-- Formal étaleness is the existence of a unique dotted lift against every affine
first-order thickening. -/
theorem formallyEtale_iff {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G) :
    FormallyEtale a ↔
      ∀ {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (i : T ⟶ T')
        [IsFirstOrderThickening i.left] (x : F.obj (op T)) (y : G.obj (op T')),
        a.app (op T) x = G.map (op i) y → ∃! x' : F.obj (op T'), liftPair a i x' = (x, y) := sorry

/-- Formal unramifiedness is injectivity of `liftPair` along every affine first-order
thickening. -/
theorem formallyUnramified_iff {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G) :
    FormallyUnramified a ↔
      ∀ {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (i : T ⟶ T')
        [IsFirstOrderThickening i.left], Function.Injective (liftPair a i) := sorry

namespace FormallySmooth

/-- The identity transformation is formally smooth. -/
instance id {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type v) : FormallySmooth (𝟙 F) := sorry

/-- A formally smooth transformation has the right lifting property against the Yoneda
image of every affine first-order thickening. -/
instance hasLiftingProperty {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    {a : F ⟶ G} [FormallySmooth a] {T T' : Over S} [IsAffine T.left] [IsAffine T'.left]
    (i : T ⟶ T') [IsFirstOrderThickening i.left] :
    HasLiftingProperty (yoneda.map i) a := sorry

end FormallySmooth

namespace FormallyEtale

/-- The identity transformation is formally étale. -/
instance id {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type v) : FormallyEtale (𝟙 F) := sorry

/-- A formally étale transformation is formally smooth. -/
instance (priority := 100) toFormallySmooth {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v}
    {a : F ⟶ G} [FormallyEtale a] : FormallySmooth a := sorry

/-- A formally étale transformation is formally unramified. -/
instance (priority := 100) toFormallyUnramified {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v}
    {a : F ⟶ G} [FormallyEtale a] : FormallyUnramified a := sorry

/-- Formal étaleness is equivalent to being both formally smooth and formally unramified. -/
theorem iff_formallySmooth_and_formallyUnramified {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G) :
    FormallyEtale a ↔ FormallySmooth a ∧ FormallyUnramified a := sorry

/-- A formally étale transformation has a unique Yoneda lift through every affine
first-order thickening. -/
theorem existsUnique_liftStruct {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    {a : F ⟶ G} [FormallyEtale a] {T T' : Over S} [IsAffine T.left] [IsAffine T'.left]
    (i : T ⟶ T') [IsFirstOrderThickening i.left] {f : yoneda.obj T ⟶ F}
    {g : yoneda.obj T' ⟶ G} (sq : CommSq f (yoneda.map i) a g) :
    Nonempty (Unique sq.LiftStruct) := sorry

end FormallyEtale

namespace FormallyUnramified

/-- The identity transformation is formally unramified. -/
instance id {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type v) : FormallyUnramified (𝟙 F) := sorry

/-- Sections of a formally unramified transformation that restrict equally along an
affine first-order thickening and have the same image under `a` are equal. -/
theorem hom_ext {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} {a : F ⟶ G}
    [FormallyUnramified a] {T T' : Over S} [IsAffine T.left] [IsAffine T'.left]
    (i : T ⟶ T') [IsFirstOrderThickening i.left] {x₁ x₂ : F.obj (op T')}
    (h : liftPair a i x₁ = liftPair a i x₂) : x₁ = x₂ := sorry

/-- Yoneda lifts of a formally unramified transformation through an affine first-order
thickening are unique whenever they exist. -/
instance subsingleton_liftStruct {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    {a : F ⟶ G} [FormallyUnramified a] {T T' : Over S} [IsAffine T.left] [IsAffine T'.left]
    (i : T ⟶ T') [IsFirstOrderThickening i.left] {f : yoneda.obj T ⟶ F}
    {g : yoneda.obj T' ⟶ G} (sq : CommSq f (yoneda.map i) a g) :
    Subsingleton sq.LiftStruct := sorry

end FormallyUnramified

end AlgebraicGeometry.Scheme.Over
