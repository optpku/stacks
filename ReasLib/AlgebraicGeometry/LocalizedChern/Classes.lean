/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.Deformation
public import ReasLib.AlgebraicGeometry.BivariantClass.Nonnegative.Rational

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- The canonical localized Newton class obtained from the graph deformation. -/
noncomputable def newtonClass
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E)) (finiteness : TechnicalCondition X E)
    (p : ℕ) :
    BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ)  :=
  graphLocalizedClass i classes (Situation.vanishing perfect vanishing finiteness)

/-- The localized Newton class in integer degree, extended by zero in negative degrees. -/
noncomputable def newtonClassInteger
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E)) (finiteness : TechnicalCondition X E)
    (p : ℤ) :
    BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p :=
  match p with
  | .ofNat n => newtonClass i classes E perfect vanishing finiteness n
  | .negSucc n =>
      BivariantClass.pointwiseZero δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (.negSucc n)

/-- In nonnegative integer degree, the extended Newton class is the canonical Newton class. -/
theorem newtonClassInteger_ofNat
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E)) (finiteness : TechnicalCondition X E)
    (p : ℕ) :
    newtonClassInteger i classes E perfect vanishing finiteness (Int.ofNat p) =
      newtonClass i classes E perfect vanishing finiteness p := rfl

/-- In negative degree, the extended Newton class is the pointwise-zero bivariant class. -/
theorem newtonClassInteger_negSucc
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E)) (finiteness : TechnicalCondition X E)
    (p : ℕ) :
    newtonClassInteger i classes E perfect vanishing finiteness (Int.negSucc p) =
      BivariantClass.pointwiseZero δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (Int.negSucc p) := rfl

/-- The canonical localized Newton class is represented by the graph deformation construction. -/
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
      (newtonClass i classes E perfect vanishing finiteness p) := by
  exact ⟨ClassConstruction.fromSituation classes E p .vanishing
    (Situation.vanishing perfect vanishing finiteness), rfl⟩

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
    BivariantClass.properPushforwardToTarget δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ Over.mk X.hom) (p : ℤ)
        (newtonClass i classes E perfect vanishing finiteness p) =
      ChernClass.Derived.newtonClass δ X.hom classes E perfect
        ((Situation.vanishing perfect vanishing finiteness :
          Situation S δ X i E p .vanishing).isDefined) p :=
  graphLocalizedClass_newton_pushforward i classes
    (Situation.vanishing perfect vanishing finiteness)

/-- The localized Chern character with degree-`p` component `Pₚ(Z ⟶ X, E) / p!`. -/
def rationalCharacter
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E)) (finiteness : TechnicalCondition X E) :
    BivariantClass.Nonnegative.Rational.Completion δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) :=
  fun p ↦ BivariantClass.Nonnegative.Rational.tensor δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p
    (newtonClass i classes E perfect vanishing finiteness p) ((p.factorial : ℚ)⁻¹)

/-- Evaluation of the localized Chern character gives `Pₚ(Z ⟶ X, E) / p!`. -/
theorem rationalCharacter_apply
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E)) (finiteness : TechnicalCondition X E)
    (p : ℕ) :
    rationalCharacter i classes E perfect vanishing finiteness p =
      BivariantClass.Nonnegative.Rational.tensor δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p (newtonClass i classes E perfect vanishing finiteness p)
        ((p.factorial : ℚ)⁻¹) := rfl

/-- The localized `p`th Chern class obtained from the graph deformation. -/
noncomputable def chernClass
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E) (p : ℕ)
    (rankBound : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      (restrictAway i E) 0 p) (finiteness : TechnicalCondition X E) :
    BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ)  :=
  graphLocalizedClass i classes (Situation.rankBound perfect rankBound finiteness)

/-- The canonical localized Chern class is represented by the graph deformation construction. -/
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
      (chernClass i classes E perfect p rankBound finiteness) := by
  exact ⟨ClassConstruction.fromSituation classes E p .rankBound
    (Situation.rankBound perfect rankBound finiteness), rfl⟩

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
    BivariantClass.properPushforwardToTarget δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ Over.mk X.hom) (p : ℤ)
        (chernClass i classes E perfect p rankBound finiteness) =
      ChernClass.Derived.totalClass δ X.hom classes E perfect
        ((Situation.rankBound perfect rankBound finiteness :
          Situation S δ X i E p .rankBound).isDefined) p :=
  graphLocalizedClass_chern_pushforward i classes
    (Situation.rankBound perfect rankBound finiteness)

end AlgebraicGeometry.LocalizedChern
