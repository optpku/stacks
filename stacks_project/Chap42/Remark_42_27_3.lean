module

public import ReasLib.AlgebraicGeometry.ChowGroup.FirstHigher
public import ReasLib.AlgebraicGeometry.ChowGroup.FirstHigher.Localization
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- The first Milnor higher Chow group `CH^M_k(X, 1)` is the middle homology of the primed
Milnor complex of Remark 42.27.2, using the presentation of ordinary Chow groups in
Remark 42.19.2. The superscript `M` distinguishes these groups from Bloch's higher Chow groups.
The base and relative dimension function are those of Situation 42.7.1. -/
#check (AlgebraicGeometry.ChowGroup.firstHigher :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ), Type u)

#check (AlgebraicGeometry.ChowGroup.firstHigherIso :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ),
    AddCommGrpCat.of (ChowGroup.firstHigher p δ k) ≅ (ChowGroup.milnorComplex p δ k).homology)

/- For an open subscheme `U` and its reduced closed complement `Y`, the primed locally finite
Milnor coefficient sequences in degrees two, one, and zero are split short exact.
The morphisms `FirstHigher.milnorComplexClosedPushforward` and
`FirstHigher.milnorComplexOpenPullback` express compatibility with both boundaries. -/
#check (AlgebraicGeometry.ChowGroup.degreeTwoLocalization_splitShortExact :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (U : X.Opens) (k : ℤ),
    (ChowGroup.Pointwise.degreeTwoLocalizationComplex p δ U k).ShortExact ∧
      (ChowGroup.Pointwise.degreeTwoOpenPullback p δ U k).comp
          (ChowGroup.Pointwise.degreeTwoExtendByZero p δ U k) = AddMonoidHom.id _)

#check (AlgebraicGeometry.ChowGroup.degreeOneLocalization_splitShortExact :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (U : X.Opens) (k : ℤ),
    (ChowGroup.Pointwise.degreeOneLocalizationComplex p δ U k).ShortExact ∧
      (ChowGroup.Pointwise.degreeOneOpenPullback p δ U k).comp
          (ChowGroup.Pointwise.degreeOneExtendByZero p δ U k) = AddMonoidHom.id _)

#check (AlgebraicGeometry.ChowGroup.degreeZeroLocalization_splitShortExact :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (U : X.Opens) (k : ℤ),
    (ChowGroup.Pointwise.degreeZeroLocalizationComplex p δ U k).ShortExact ∧
      (ChowGroup.Pointwise.degreeZeroOpenPullback p δ U k).comp
          (ChowGroup.Pointwise.degreeZeroExtendByZero p δ U k) = AddMonoidHom.id _)

/- Remark 42.27.3: applying the snake lemma (Homology, Lemma 12.13.6) to the compatible
split short exact coefficient sequences gives
`CH^M_k(Y, 1) ⟶ CH^M_k(X, 1) ⟶ CH^M_k(U, 1) ⟶ CH_k(Y) ⟶ CH_k(X) ⟶ CH_k(U) ⟶ 0`,
extending the canonical localization sequence of Lemma 42.19.3.
The source also discusses defining flat pullback and proper pushforward with further work;
that final sentence is prospective and asserts no such additional construction here. -/
@[stacks 0GUA] #check (AlgebraicGeometry.ChowGroup.localization_exact :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (U : X.Opens) (k : ℤ),
    (ChowGroup.FirstHigher.localizationArrows p δ U k).Exact ∧
      Epi (ChowGroup.Localization.complex p δ U k).g)
