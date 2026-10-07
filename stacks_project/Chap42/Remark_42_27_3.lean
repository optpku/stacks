module

public import stacks_project.Chap42.Remark_42_27_2
public import stacks_project.Chap42.Remark_42_27_3_FirstHigher
public import stacks_project.Chap42.Remark_42_27_3_Localization

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- Remark 42.27.3 (1): under Situation 42.7.1, if `X` is locally of finite type over `S` and
`k : ℤ`, the first higher Chow group `CH^M_k(X, 1)` is the homology `H_1` of the primed Milnor
complex of Remark 42.27.2. The superscript `M` distinguishes this group from the higher Chow
groups of Bloch. -/
@[stacks 0GUA]
abbrev firstHigher {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
    [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ) : Type u :=
  @Pointwise.firstHigher X (LocallyOfFiniteType.isLocallyNoetherian p)
    (p.relativeDimensionFunction δ) inferInstance k

/-- The Situation 42.7.1 first higher Chow group is the homology of the primed Milnor complex. -/
def firstHigherIso {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
    [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ) :
    AddCommGrpCat.of (firstHigher p δ k) ≅ (milnorComplex p δ k).homology :=
  @Pointwise.firstHigherIso X (LocallyOfFiniteType.isLocallyNoetherian p)
    (p.relativeDimensionFunction δ) inferInstance k

/-- Remark 42.27.3 (2): for `i = 2`, the primed products of `K₂ᴹ` along an open subscheme and
its reduced closed complement form a split short exact sequence, compatible with the first
boundary of Remark 42.27.2. -/
@[stacks 0GUA]
theorem degreeTwoLocalization_splitShortExact {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]
    (U : X.Opens) (k : ℤ) :
    (Pointwise.degreeTwoLocalizationComplex p δ U k).ShortExact ∧
      (Pointwise.degreeTwoOpenPullback p δ U k).comp
          (Pointwise.degreeTwoExtendByZero p δ U k) =
        AddMonoidHom.id _ := sorry

/-- Remark 42.27.3 (3): for `i = 1`, the primed products of `K₁ᴹ` along an open subscheme and
its reduced closed complement form a split short exact sequence, compatible with the boundaries
of Remark 42.27.2. -/
@[stacks 0GUA]
theorem degreeOneLocalization_splitShortExact {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]
    (U : X.Opens) (k : ℤ) :
    (Pointwise.degreeOneLocalizationComplex p δ U k).ShortExact ∧
      (Pointwise.degreeOneOpenPullback p δ U k).comp
          (Pointwise.degreeOneExtendByZero p δ U k) =
        AddMonoidHom.id _ := sorry

/-- Remark 42.27.3 (4): for `i = 0`, the primed products of `K₀ᴹ` along an open subscheme and
its reduced closed complement form a split short exact sequence, compatible with the second
boundary of Remark 42.27.2. -/
@[stacks 0GUA]
theorem degreeZeroLocalization_splitShortExact {S X : Scheme.{u}} (p : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]
    (U : X.Opens) (k : ℤ) :
    (Pointwise.degreeZeroLocalizationComplex p δ U k).ShortExact ∧
      (Pointwise.degreeZeroOpenPullback p δ U k).comp
          (Pointwise.degreeZeroExtendByZero p δ U k) =
        AddMonoidHom.id _ := sorry

/-- Remark 42.27.3 (5): applying the snake lemma to the compatible split short exact sequences of
primed products yields a six-term exact sequence
`CH^M_k(Y, 1) ⟶ CH^M_k(X, 1) ⟶ CH^M_k(U, 1) ⟶ CH_k(Y) ⟶ CH_k(X) ⟶ CH_k(U) ⟶ 0`
extending Lemma 42.19.3. -/
@[stacks 0GUA]
theorem localization_exact {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
    [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ] (U : X.Opens) (k : ℤ) :
    (FirstHigher.localizationArrows p δ U k).Exact ∧
      Epi (Localization.complex p δ U k).g := sorry

end AlgebraicGeometry.ChowGroup
