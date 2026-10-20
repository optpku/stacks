/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap42.Lemma_42_47_2_Independence
public import stacks_project.Chap42.Lemma_42_48_3
public import stacks_project.Chap42.Lemma_42_48_4
public import stacks_project.Chap42.Lemma_42_49_2_Construction

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- The inverse image in the infinity fibre of a closed subscheme of `X`. -/
abbrev infinityCenter
    {S : Scheme.{u}} {X : Over S} {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) (b : W ⟶ ProjectiveLineFamily.space X) : Over S :=
  pullback (BivariantClass.GysinAtInfinity.infinityToX X b)
    (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)

/-- The canonical square defining `infinityCenter i b` is cartesian. -/
theorem infinityCenter_isPullback
    {S : Scheme.{u}} {X : Over S} {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) (b : W ⟶ ProjectiveLineFamily.space X) :
    IsPullback
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left
      (pullback.snd (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left
      (BivariantClass.GysinAtInfinity.infinityToX X b).left i := sorry

/-- The canonical comparison from the source convention used by `IsLocalizedExtension`
to the chosen pullback object `infinityCenter i b`. -/
abbrev infinityCenterComparison
    {S : Scheme.{u}} {X : Over S} {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) (b : W ⟶ ProjectiveLineFamily.space X) :
    Over.mk
        ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
            (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
          (BivariantClass.GysinAtInfinity.infinityFiber X b).hom) ⟶
      infinityCenter i b :=
  Over.homMk (𝟙 _)
    ((Category.id_comp _).trans
      (Over.w (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))).symm)

/-- The comparison to `infinityCenter i b` is the identity on underlying schemes. -/
theorem infinityCenterComparison_left
    {S : Scheme.{u}} {X : Over S} {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) (b : W ⟶ ProjectiveLineFamily.space X) :
    (infinityCenterComparison i b).left = 𝟙 _ := sorry

/-- The identity-on-underlying-scheme comparison is locally of finite type. -/
instance infinityCenterComparisonLocallyOfFiniteType
    {S : Scheme.{u}} {X : Over S} {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) (b : W ⟶ ProjectiveLineFamily.space X) :
    LocallyOfFiniteType (infinityCenterComparison i b).left := sorry

/-- Reindex a class on the canonical infinity center to the source convention used by
`IsLocalizedExtension`. -/
def localizedClassForExtension
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (p : ℤ)
    (localized : BivariantClass delta
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) p) :
    BivariantClass delta
      (Over.homMk
        (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left :
        Over.mk
            ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
                (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
              (BivariantClass.GysinAtInfinity.infinityFiber X b).hom) ⟶
          BivariantClass.GysinAtInfinity.infinityFiber X b) p :=
  BivariantClass.restrict delta (infinityCenterComparison i b)
    (Over.homMk
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left)
    (𝟙 _) IsPullback.of_id_fst p localized

/-- `localizedClassForExtension` is restriction along the canonical identity comparison. -/
theorem localizedClassForExtension_def
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (p : ℤ)
    (localized : BivariantClass delta
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) p) :
    localizedClassForExtension delta i b p localized =
      BivariantClass.restrict delta (infinityCenterComparison i b)
        (Over.homMk
          (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
            (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left)
        (𝟙 _) IsPullback.of_id_fst p localized := sorry

/-- Reindex an identity class on the canonical infinity center to the identity-class
convention used by `IsLocalizedExtension`. -/
def ambientClassForExtension
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (p : ℤ) (ambient : BivariantClass delta (𝟙 (infinityCenter i b)) p) :
    BivariantClass delta
      (𝟙 (Over.mk
        ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
            (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
          (BivariantClass.GysinAtInfinity.infinityFiber X b).hom))) p :=
  BivariantClass.restrict delta (infinityCenterComparison i b) (𝟙 _)
    (infinityCenterComparison i b) IsPullback.of_id_snd p ambient

/-- `ambientClassForExtension` is restriction along the canonical identity comparison. -/
theorem ambientClassForExtension_def
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (p : ℤ) (ambient : BivariantClass delta (𝟙 (infinityCenter i b)) p) :
    ambientClassForExtension delta i b p ambient =
      BivariantClass.restrict delta (infinityCenterComparison i b) (𝟙 _)
        (infinityCenterComparison i b) IsPullback.of_id_snd p ambient := sorry

/-- A localized extension expressed on the canonical pullback representation of the
infinity center. -/
def IsInfinityLocalizedExtension
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W T : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    [IsClosedImmersion
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left]
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t]
    (p : ℤ) (ambient : BivariantClass delta (𝟙 (infinityCenter i b)) p)
    (localized : BivariantClass delta
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) p) : Prop :=
  BivariantClass.IsLocalizedExtension delta
    (BivariantClass.GysinAtInfinity.infinityFiber X b) t
    (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left p
    (ambientClassForExtension delta i b p ambient)
    (localizedClassForExtension delta i b p localized)

/-- The canonical-pullback localized-extension predicate unfolds to the transported
`BivariantClass.IsLocalizedExtension` specification. -/
theorem isInfinityLocalizedExtension_iff
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W T : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    [IsClosedImmersion
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left]
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t]
    (p : ℤ) (ambient : BivariantClass delta (𝟙 (infinityCenter i b)) p)
    (localized : BivariantClass delta
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) p) :
    IsInfinityLocalizedExtension delta i b t p ambient localized ↔
      BivariantClass.IsLocalizedExtension delta
        (BivariantClass.GysinAtInfinity.infinityFiber X b) t
        (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left p
        (ambientClassForExtension delta i b p ambient)
        (localizedClassForExtension delta i b p localized) := sorry

/-- The bivariant class at zero obtained by composing a localized infinity class with
the Gysin-at-infinity class and pushing forward from the inverse image of `Z`. -/
def classAtZero
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (p : ℤ)
    (localized : BivariantClass delta
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) p) :
    BivariantClass delta (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p :=
  BivariantClass.pushforwardComp delta
    (pullback.snd (BivariantClass.GysinAtInfinity.infinityToX X b)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))
    (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
    (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))
    (BivariantClass.GysinAtInfinity.infinityToX X b) pullback.condition p localized
    (BivariantClass.gysinAtInfinity delta X b)

/-- `classAtZero` is the canonical pushforward-after-composition construction. -/
theorem classAtZero_def
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (p : ℤ)
    (localized : BivariantClass delta
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) p) :
    classAtZero delta i b p localized =
      BivariantClass.pushforwardComp delta
        (pullback.snd (BivariantClass.GysinAtInfinity.infinityToX X b)
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
        (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))
        (BivariantClass.GysinAtInfinity.infinityToX X b) pullback.condition p localized
        (BivariantClass.gysinAtInfinity delta X b) := sorry

/-- Equal localized classes determine equal classes at zero. -/
theorem classAtZero_congr
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (p : ℤ)
    {localized localized' : BivariantClass delta
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) p}
    (h : localized = localized') :
    classAtZero delta i b p localized = classAtZero delta i b p localized' := sorry

/-- The compatibility needed to map between inverse images in two infinity fibres. -/
theorem infinityCenterMap_comm
    {S : Scheme.{u}} {X : Over S} {Z W W' : Scheme.{u}}
    (i : Z ⟶ X.left)
    (b : W ⟶ ProjectiveLineFamily.space X)
    (b' : W' ⟶ ProjectiveLineFamily.space X)
    (gInf : BivariantClass.GysinAtInfinity.infinityFiber X b' ⟶
      BivariantClass.GysinAtInfinity.infinityFiber X b)
    (hInf : gInf ≫ BivariantClass.GysinAtInfinity.infinityToX X b =
      BivariantClass.GysinAtInfinity.infinityToX X b') :
    (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b')
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) ≫ gInf) ≫
        BivariantClass.GysinAtInfinity.infinityToX X b =
      pullback.snd (BivariantClass.GysinAtInfinity.infinityToX X b')
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) ≫
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) := sorry

/-- The canonical map between infinity centers induced by a map of infinity fibres. -/
def infinityCenterMap
    {S : Scheme.{u}} {X : Over S} {Z W W' : Scheme.{u}}
    (i : Z ⟶ X.left)
    (b : W ⟶ ProjectiveLineFamily.space X)
    (b' : W' ⟶ ProjectiveLineFamily.space X)
    (gInf : BivariantClass.GysinAtInfinity.infinityFiber X b' ⟶
      BivariantClass.GysinAtInfinity.infinityFiber X b)
    (hInf : gInf ≫ BivariantClass.GysinAtInfinity.infinityToX X b =
      BivariantClass.GysinAtInfinity.infinityToX X b') :
    infinityCenter i b' ⟶ infinityCenter i b :=
  pullback.lift
    (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b')
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) ≫ gInf)
    (pullback.snd (BivariantClass.GysinAtInfinity.infinityToX X b')
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))
    (infinityCenterMap_comm i b b' gInf hInf)

/-- The infinity-center comparison has the expected projection to the infinity fibre. -/
theorem infinityCenterMap_fst
    {S : Scheme.{u}} {X : Over S} {Z W W' : Scheme.{u}}
    (i : Z ⟶ X.left)
    (b : W ⟶ ProjectiveLineFamily.space X)
    (b' : W' ⟶ ProjectiveLineFamily.space X)
    (gInf : BivariantClass.GysinAtInfinity.infinityFiber X b' ⟶
      BivariantClass.GysinAtInfinity.infinityFiber X b)
    (hInf : gInf ≫ BivariantClass.GysinAtInfinity.infinityToX X b =
      BivariantClass.GysinAtInfinity.infinityToX X b') :
    infinityCenterMap i b b' gInf hInf ≫
        pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) =
      pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b')
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) ≫ gInf := sorry

/-- The infinity-center comparison has identity projection to the fixed center `Z`. -/
theorem infinityCenterMap_snd
    {S : Scheme.{u}} {X : Over S} {Z W W' : Scheme.{u}}
    (i : Z ⟶ X.left)
    (b : W ⟶ ProjectiveLineFamily.space X)
    (b' : W' ⟶ ProjectiveLineFamily.space X)
    (gInf : BivariantClass.GysinAtInfinity.infinityFiber X b' ⟶
      BivariantClass.GysinAtInfinity.infinityFiber X b)
    (hInf : gInf ≫ BivariantClass.GysinAtInfinity.infinityToX X b =
      BivariantClass.GysinAtInfinity.infinityToX X b') :
    infinityCenterMap i b b' gInf hInf ≫
        pullback.snd (BivariantClass.GysinAtInfinity.infinityToX X b)
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) =
      pullback.snd (BivariantClass.GysinAtInfinity.infinityToX X b')
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) := sorry

/-- The square relating the infinity-center comparison to the infinity-fibre map is
cartesian. -/
theorem infinityCenterMap_isPullback
    {S : Scheme.{u}} {X : Over S} {Z W W' : Scheme.{u}}
    (i : Z ⟶ X.left)
    (b : W ⟶ ProjectiveLineFamily.space X)
    (b' : W' ⟶ ProjectiveLineFamily.space X)
    (gInf : BivariantClass.GysinAtInfinity.infinityFiber X b' ⟶
      BivariantClass.GysinAtInfinity.infinityFiber X b)
    (hInf : gInf ≫ BivariantClass.GysinAtInfinity.infinityToX X b =
      BivariantClass.GysinAtInfinity.infinityToX X b') :
    IsPullback (infinityCenterMap i b b' gInf hInf).left
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b')
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left gInf.left := sorry

/-- A proper map of infinity fibres induces a proper map of their inverse images of `Z`. -/
instance infinityCenterMapIsProper
    {S : Scheme.{u}} {X : Over S} {Z W W' : Scheme.{u}}
    (i : Z ⟶ X.left)
    (b : W ⟶ ProjectiveLineFamily.space X)
    (b' : W' ⟶ ProjectiveLineFamily.space X)
    (gInf : BivariantClass.GysinAtInfinity.infinityFiber X b' ⟶
      BivariantClass.GysinAtInfinity.infinityFiber X b) [IsProper gInf.left]
    (hInf : gInf ≫ BivariantClass.GysinAtInfinity.infinityToX X b =
      BivariantClass.GysinAtInfinity.infinityToX X b') :
    IsProper (infinityCenterMap i b b' gInf hInf).left := sorry

/-- Restriction of the localized class and proper pushforward of the degree-zero infinity
class imply invariance of the assembled class at zero. -/
theorem classAtZero_eq_of_modification
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W W' : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (b' : W' ⟶ ProjectiveLineFamily.space X) [IsProper b']
    [IsIso (b' ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (gInf : BivariantClass.GysinAtInfinity.infinityFiber X b' ⟶
      BivariantClass.GysinAtInfinity.infinityFiber X b) [IsProper gInf.left]
    (hInf : gInf ≫ BivariantClass.GysinAtInfinity.infinityToX X b =
      BivariantClass.GysinAtInfinity.infinityToX X b')
    (p : ℤ)
    (localized : BivariantClass delta
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) p)
    (localized' : BivariantClass delta
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b')
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) p)
    (localizedPullback : localized' = BivariantClass.restrict delta
      (infinityCenterMap i b b' gInf hInf)
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b')
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))
      gInf (infinityCenterMap_isPullback i b b' gInf hInf) p localized)
    (gysinPushforward : BivariantClass.pushforward delta gInf
      (BivariantClass.GysinAtInfinity.infinityToX X b) 0
      (hInf.symm ▸ BivariantClass.gysinAtInfinity delta X b') =
        BivariantClass.gysinAtInfinity delta X b) :
    classAtZero delta i b' p localized' = classAtZero delta i b p localized := sorry

end AlgebraicGeometry.LocalizedChern
