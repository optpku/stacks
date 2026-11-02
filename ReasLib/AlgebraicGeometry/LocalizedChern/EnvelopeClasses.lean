/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.DerivedEnvelopeCaps
public import ReasLib.AlgebraicGeometry.LocalizedChern.BaseChange
public import ReasLib.AlgebraicGeometry.LocalizedChern.Mixed
public import ReasLib.AlgebraicGeometry.BivariantClass.Cutoff.Completion
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Pullback

/-!
# Localized Chern classes by envelope descent

The cap operation is descended from the ordinary localized classes of all actual
finite locally free envelope models, with values on the inverse-image center.
The mixed series extends the graph-defined series to every perfect object with
an envelope representative. The construction uses schemes and the existing Chow
theory; extension to ringed topoi requires an analogous intersection theory.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern.EnvelopeClasses

variable {S : Scheme.{u}} [UniversallyCatenary S]
variable {δ : S → ℤ} [IsDimensionFunction δ]
variable {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
variable (i : Z ⟶ X.left) [IsClosedImmersion i]
variable (classes : ChernClass.Theory δ X.hom)
variable (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
variable (perfect : RingedSpace.ModuleDerived.IsPerfect E)
variable (defined : ChernClass.Derived.IsDefined E)
variable (p : ℕ)
variable (rankBound : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
  (restrictAway i E) 0 p)

section Models

variable {V W : Over S} [LocallyOfFiniteType V.hom] [LocallyOfFiniteType W.hom]
variable (g : V ⟶ X) (j : W ⟶ V) [IsClosedImmersion j.left]
variable (a : W ⟶ Over.mk (i ≫ X.hom))
variable (square : IsPullback a.left j.left i g.left)

include rankBound square in
/-- The pullback of an envelope model satisfies the original strict rank bound
away from the inverse-image closed center. -/
theorem model_rankBound (m : EnvelopeCaps.Model E V g) :
    Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      (restrictAway (pullback.snd j.left m.map.left)
        ((RingedSpace.modulePullbackDerived (m.map ≫ g).left.toShHom).obj E)) 0 p :=
  sorry

/-- The additive sum of localized model cap operations followed by proper
pushforward from their inverse-image centers. -/
def beforeDescent (k : ℤ) :
    (⨁ m : EnvelopeCaps.Model E V g, EnvelopeCaps.ModelChow δ E g k m) →+
      RelativeChow δ W (k - (p : ℤ)) := by
  classical
  exact DirectSum.toAddMonoid fun m => by
    -- Local instance justification (defeq pin): use the finite-type proof stored in the model.
    letI := m.finiteType
    -- Local instance justification (proof-local temporary data): the model's envelope is proper.
    letI := m.envelope.toIsProper
    let center : Over S := Over.mk (pullback.snd j.left m.map.left ≫ m.Y.hom)
    let inclusion : center ⟶ m.Y := Over.homMk (pullback.snd j.left m.map.left)
    let projection : center ⟶ W := Over.homMk (pullback.fst j.left m.map.left) (by
      change pullback.fst j.left m.map.left ≫ W.hom =
        pullback.snd j.left m.map.left ≫ m.Y.hom
      rw [← Over.w j, ← Category.assoc, pullback.condition, Category.assoc, Over.w m.map])
    have projectionProper : IsProper projection.left := by
      change IsProper (pullback.fst j.left m.map.left)
      infer_instance
    let modelE := (RingedSpace.modulePullbackDerived (m.map ≫ g).left.toShHom).obj E
    have modelPerfect : RingedSpace.ModuleDerived.IsPerfect modelE :=
      RingedSpace.modulePullbackDerived_isPerfect _ E perfect
    have modelFinite : TechnicalCondition m.Y modelE :=
      .hasRepresentative ⟨m.complex, m.represents, m.above, m.below, m.free⟩
    let c := LocalizedChern.chernClass inclusion.left (classes.reanchor m.Y)
      modelE modelPerfect p (model_rankBound i E p rankBound g j a square m) modelFinite
    exact (@ChowGroup.map S _ δ _ center W inferInstance inferInstance
      projection projectionProper (k - (p : ℤ))).comp
      (c.cap (𝟙 center) inclusion (𝟙 m.Y)
        (IsPullback.id_horiz inclusion.left) k)

include defined in
/-- The sum of model cap operations annihilates the kernel of the sum of envelope
pushforwards. -/
theorem beforeDescent_kills_kernel (k : ℤ) :
    (EnvelopeCaps.coverMap δ E g k).ker ≤
      (beforeDescent i classes E perfect p rankBound g j a square k).ker := sorry

/-- The localized cap operation descended through the envelope pushforward map
using its explicit cycle-lifting right inverse. -/
def capAt (k : ℤ) : RelativeChow δ V k →+ RelativeChow δ W (k - (p : ℤ)) :=
  (EnvelopeCaps.coverMap δ E g k).liftOfRightInverse
    (EnvelopeCaps.coverPreimage δ E g defined k)
    (EnvelopeCaps.coverPreimage_rightInverse δ E g defined k)
    ⟨beforeDescent i classes E perfect p rankBound g j a square k,
      beforeDescent_kills_kernel i classes E perfect defined p rankBound g j a square k⟩

end Models

/-- The cartesian-square-indexed localized cap maps obtained by envelope descent. -/
def capFamily :
    BivariantClass.CapFamily δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ) :=
  fun {_ _} _ _ a j g _ square k => by
    -- Local instance justification (proof-local temporary data): a cartesian inverse image of the closed center is closed.
    letI : IsClosedImmersion j.left :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) square inferInstance
    exact capAt i classes E perfect defined p rankBound g j a square k

/-- The descended localized cap maps commute with proper pushforward. -/
theorem cap_proper : BivariantClass.CompatibleWithProperPushforward δ
    (capFamily i classes E perfect defined p rankBound) := sorry

/-- The descended localized cap maps commute with flat pullback. -/
theorem cap_flat : BivariantClass.CompatibleWithFlatPullback δ
    (capFamily i classes E perfect defined p rankBound) := sorry

/-- The descended localized cap maps commute with effective-Cartier Gysin pullback. -/
theorem cap_gysin : BivariantClass.CompatibleWithCartierGysin δ
    (capFamily i classes E perfect defined p rankBound) := sorry

/-- The localized Chern class of an envelope-defined perfect derived module with
a strict degree-zero rank bound away from the closed center. -/
def chernClass :
    BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ) where
  cap := capFamily i classes E perfect defined p rankBound
  map_proper := cap_proper i classes E perfect defined p rankBound
  pullback_flat := cap_flat i classes E perfect defined p rankBound
  gysin_cartier := cap_gysin i classes E perfect defined p rankBound

/-- On a sum of actual envelope model classes, the descended localized cap is the
sum of the ordinary model caps followed by proper pushforward from the centers. -/
theorem chernClass_spec
    {V W : Over S} [LocallyOfFiniteType V.hom] [LocallyOfFiniteType W.hom]
    (g : V ⟶ X) [LocallyOfFiniteType g.left]
    (j : W ⟶ V) [IsClosedImmersion j.left]
    (a : W ⟶ Over.mk (i ≫ X.hom))
    (square : IsPullback a.left j.left i g.left) (k : ℤ)
    (z : ⨁ m : EnvelopeCaps.Model E V g, EnvelopeCaps.ModelChow δ E g k m) :
    (chernClass i classes E perfect defined p rankBound).cap a j g square k
        (EnvelopeCaps.coverMap δ E g k z) =
      beforeDescent i classes E perfect p rankBound g j a square k z :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

/-- Proper pushforward of the descended localized Chern class is the ambient
derived Chern class. -/
theorem chernClass_pushforward :
    BivariantClass.properPushforwardToTarget δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ)
      (chernClass i classes E perfect defined p rankBound) =
    ChernClass.Derived.totalClass δ X.hom classes E perfect defined p := sorry

/-- On the graph-construction domain the envelope-descended localized Chern class
agrees with the graph-defined localized class. -/
theorem chernClass_eq (finiteness : TechnicalCondition X E) :
    chernClass i classes E perfect defined p rankBound =
      LocalizedChern.chernClass i classes E perfect p rankBound finiteness := sorry

/-- The mixed Chern family uses ambient total Chern classes below the cutoff and
envelope-descended localized classes from the cutoff onward. -/
def mixedChernClass :
    BivariantClass.Cutoff.Family δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p :=
  fun n => if h : n < p then
    BivariantClass.Cutoff.ofAmbient δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (Nat.cast_lt.mpr h)
      (ChernClass.Derived.totalClass δ X.hom classes E perfect defined n)
  else
    BivariantClass.Cutoff.ofRelative δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
      (not_lt.mpr (Nat.cast_le.mpr (le_of_not_gt h)))
      (chernClass i classes E perfect defined n
        (by
          obtain ⟨hiso, hfree, hrank⟩ := rankBound
          exact ⟨hiso, hfree, fun x => lt_of_lt_of_le (hrank x) (le_of_not_gt h)⟩))

/-- Below the cutoff the mixed family is the ambient total Chern class. -/
theorem mixedChernClass_of_lt {n : ℕ} (h : n < p) :
    mixedChernClass i classes E perfect defined p rankBound n =
      BivariantClass.Cutoff.ofAmbient δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (Nat.cast_lt.mpr h)
        (ChernClass.Derived.totalClass δ X.hom classes E perfect defined n) := by
  simp only [mixedChernClass, dif_pos h]

/-- At or above the cutoff the mixed family is the descended localized Chern class. -/
theorem mixedChernClass_of_ge {n : ℕ} (h : p ≤ n) :
    mixedChernClass i classes E perfect defined p rankBound n =
      BivariantClass.Cutoff.ofRelative δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
        (not_lt.mpr (Nat.cast_le.mpr h))
        (chernClass i classes E perfect defined n (by
          obtain ⟨hiso, hfree, hrank⟩ := rankBound
          exact ⟨hiso, hfree, fun x => lt_of_lt_of_le (hrank x) h⟩)) := by
  simp only [mixedChernClass, dif_neg (not_lt.mpr h)]

/-- On a rank-bound localized-Chern situation, the envelope-descended mixed family
is the graph-defined mixed family. -/
theorem mixedChernClass_eq (situation : Situation S δ X i E p .rankBound) :
    mixedChernClass i classes E perfect defined p rankBound =
      LocalizedChern.mixedChernClass i classes E p situation := by
  funext n
  by_cases h : n < p
  · simp only [mixedChernClass, LocalizedChern.mixedChernClass, dif_pos h]
  · simp only [mixedChernClass, LocalizedChern.mixedChernClass, dif_neg h]
    congr 1
    exact chernClass_eq i classes E perfect defined n _ situation.finiteness

end AlgebraicGeometry.LocalizedChern.EnvelopeClasses
