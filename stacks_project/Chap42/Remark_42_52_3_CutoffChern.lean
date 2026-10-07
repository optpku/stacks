module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import stacks_project.Chap42.Remark_42_34_7_Cutoff
public import stacks_project.Chap42.Lemma_42_50_2_DefinedChern

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- The closed immersion `i` remains a closed immersion as a morphism of `S`-schemes. -/
instance instIsClosedImmersion_overHomMk
    {S : Scheme.{u}} {X : Over S} {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i] :
    IsClosedImmersion (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X).left :=
  ‹IsClosedImmersion i›


namespace Situation

/-- A rank-bound localized-Chern situation of bound `p` remains a rank-bound situation
of every larger bound `n`. -/
theorem rankBound_of_le
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    (situation : Situation S δ X i E p .rankBound) (n : ℕ) (h : p ≤ n) :
    Situation S δ X i E n .rankBound := sorry

end Situation

/-- The selected localized Chern class of `E` along `Z ⟶ X` in degree `n`, specified by
proper pushforward to the ambient Chern class `c_n(E)`. -/
noncomputable def localizedChernClass
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E) (n : ℕ)
    (rankBound : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      (restrictAway i E) 0 n) (finiteness : TechnicalCondition X E) :
    BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (n : ℤ) :=
  let f : Over.mk (i ≫ X.hom) ⟶ X := Over.homMk i
  let sit : Situation S δ X i E n RestrictionBehavior.rankBound :=
    { perfect := perfect, offCenter := rankBound, finiteness := finiteness }
  @Classical.epsilon (BivariantClass δ f (n : ℤ))
    ⟨BivariantClass.pointwiseZero δ f (n : ℤ)⟩
    (fun c : BivariantClass δ f (n : ℤ) ↦
      (BivariantClass.pushforwardToTarget δ f (n : ℤ) c :
          ChowCohomology.degree δ X.hom n) =
        ChernClass.Derived.totalClass δ X.hom classes E perfect sit.isDefined n)

/-- Proper pushforward of `localizedChernClass` recovers the ambient Chern class. -/
theorem localizedChernClass_spec
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E) (n : ℕ)
    (rankBound : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      (restrictAway i E) 0 n) (finiteness : TechnicalCondition X E) :
    (BivariantClass.pushforwardToTarget δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (n : ℤ)
        (localizedChernClass i classes E perfect n rankBound finiteness) :
      ChowCohomology.degree δ X.hom n) =
      ChernClass.Derived.totalClass δ X.hom classes E perfect
        ({ perfect := perfect, offCenter := rankBound, finiteness := finiteness } :
          Situation S δ X i E n RestrictionBehavior.rankBound).isDefined n := sorry

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
      (localizedChernClass i classes E situation.perfect n
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
          situation.isDefined n) := sorry

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
        (localizedChernClass i classes E situation.perfect n
          (Situation.rankBound_of_le situation n h).offCenter
          situation.finiteness) := sorry

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
          (localizedChernClass i classes E situation.perfect n
            (Situation.rankBound_of_le situation n (le_of_not_gt h)).offCenter
            situation.finiteness) := sorry

end AlgebraicGeometry.LocalizedChern
