/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.Classes
public import ReasLib.AlgebraicGeometry.LocalizedChern.Definedness
public import ReasLib.AlgebraicGeometry.BivariantClass.Cutoff.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Over.ClosedImmersion

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

namespace Situation

/-- A rank-bound localized-Chern situation of bound `p` remains a rank-bound situation
of every larger bound `n`. -/
theorem rankBound_of_le
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    (situation : Situation S δ X i E p .rankBound) (n : ℕ) (h : p ≤ n) :
    Situation S δ X i E n .rankBound := by
  refine ⟨situation.perfect, ?_, situation.finiteness⟩
  obtain ⟨hiso, hfree, hrank⟩ := situation.offCenter
  exact ⟨hiso, hfree, fun x ↦ lt_of_lt_of_le (hrank x) h⟩

end Situation

/-- The mixed Chern series of `E` along a closed immersion: ambient Chern classes
`c_n(E)` in degrees `n < p`, and localized Chern classes `c_n(Z ⟶ X, E)` in degrees
`p ≤ n`, as a family of cutoff degrees of `A⁽ᵖ⁾(Z ⟶ X)`. -/
noncomputable def mixedChernClass
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (situation : Situation S δ X i E p .rankBound) (n : ℕ) :
    BivariantClass.Cutoff δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p n :=
  let f : Over.mk (i ≫ X.hom) ⟶ X := Over.homMk i
  if h : n < p then
    BivariantClass.Cutoff.ofAmbient δ f (Nat.cast_lt.mpr h)
      (ChernClass.Derived.totalClass δ X.hom classes E situation.perfect
        situation.isDefined n)
  else
    BivariantClass.Cutoff.ofRelative δ f
      (not_lt.mpr (Nat.cast_le.mpr (le_of_not_gt h)))
      (chernClass i classes E situation.perfect n
        (Situation.rankBound_of_le situation n (le_of_not_gt h)).offCenter
        situation.finiteness)

/-- Below the cutoff, the mixed series is the ambient Chern class of `E`. -/
theorem mixedChernClass_of_lt
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (situation : Situation S δ X i E p .rankBound) {n : ℕ} (h : n < p) :
    mixedChernClass i classes E p situation n =
      BivariantClass.Cutoff.ofAmbient δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (Nat.cast_lt.mpr h)
        (ChernClass.Derived.totalClass δ X.hom classes E situation.perfect
          situation.isDefined n) := by
  simp only [mixedChernClass, dif_pos h]

/-- From the cutoff onward, the mixed series is the localized Chern class of `E`
along `Z ⟶ X`. -/
theorem mixedChernClass_of_ge
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (situation : Situation S δ X i E p .rankBound) {n : ℕ} (h : p ≤ n) :
    mixedChernClass i classes E p situation n =
      BivariantClass.Cutoff.ofRelative δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
        (not_lt.mpr (Nat.cast_le.mpr h))
        (chernClass i classes E situation.perfect n
          (Situation.rankBound_of_le situation n h).offCenter
          situation.finiteness) := by
  simp only [mixedChernClass, dif_neg (not_lt.mpr h)]

/-- The degree-zero term of the mixed series is the identity class of `X`, whenever the
cutoff is strictly positive. -/
theorem mixedChernClass_one
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) {p : ℕ}
    (situation : Situation S δ X i E p .rankBound) (hp : 0 < p) :
    mixedChernClass i classes E p situation 0 =
      BivariantClass.Cutoff.ofAmbient δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (Nat.cast_lt.mpr hp)
        (ChowCohomology.one δ X.hom) := sorry

/-- The mixed series is ambient Chern classes of `E` below the cutoff and localized
Chern classes along `Z ⟶ X` from the cutoff onward. -/
theorem mixedChernClass_spec
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (p : ℕ)
    (situation : Situation S δ X i E p .rankBound) (n : ℕ) :
    mixedChernClass i classes E p situation n =
      if h : n < p then
        BivariantClass.Cutoff.ofAmbient δ
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (Nat.cast_lt.mpr h)
          (ChernClass.Derived.totalClass δ X.hom classes E situation.perfect
            situation.isDefined n)
      else
        BivariantClass.Cutoff.ofRelative δ
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
          (not_lt.mpr (Nat.cast_le.mpr (le_of_not_gt h)))
          (chernClass i classes E situation.perfect n
            (Situation.rankBound_of_le situation n (le_of_not_gt h)).offCenter
            situation.finiteness) := rfl

end AlgebraicGeometry.LocalizedChern
