module

public import stacks_project.Chap42.Lemma_42_50_2
public import stacks_project.Chap42.Remark_42_34_7_Cutoff

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- A closed subscheme of an `S`-scheme locally of finite type is locally of finite
type over `S`. -/
instance closedOverSourceLocallyOfFiniteType
    {S : Scheme.{u}} {X : Over S} [LocallyOfFiniteType X.hom]
    {Z : Scheme.{u}} (i : Z ⟶ X.left) [IsClosedImmersion i] :
    LocallyOfFiniteType (Over.mk (i ≫ X.hom)).hom := sorry

/-- The closed immersion `i` remains a closed immersion as a morphism of `S`-schemes. -/
instance instIsClosedImmersion_overHomMk
    {S : Scheme.{u}} {X : Over S} {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i] :
    IsClosedImmersion (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X).left :=
  ‹IsClosedImmersion i›

/-- A zero derived module is a degree-zero vector bundle of rank strictly less than
any positive bound. -/
theorem rankBound_of_isZero {X : Scheme.{u}}
    {E : RingedSpace.ModuleDerived X.toRingedSpace}
    (hE : IsZero E) {p : ℕ} (hp : 0 < p) :
    Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree E 0 p := sorry

/-- Complementary relative degrees in the Newton recurrence add to the successor degree. -/
theorem newtonClass_succ_degree (n j : ℕ) (hj : j ∈ Finset.range n) :
    ((j + 1 : ℕ) : ℤ) + ((n - j : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) := sorry

/-- The selected localized Newton class of `E` along `Z ⟶ X` in degree `p`, specified by
proper pushforward to the ambient Newton class. -/
noncomputable def newtonClass
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E)) (finiteness : TechnicalCondition X E)
    (p : ℕ) :
    BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ) :=
  let f : Over.mk (i ≫ X.hom) ⟶ X := Over.homMk i
  let sit : Situation S δ X i E p RestrictionBehavior.vanishing :=
    { perfect := perfect, offCenter := vanishing, finiteness := finiteness }
  @Classical.epsilon (BivariantClass δ f (p : ℤ))
    ⟨BivariantClass.pointwiseZero δ f (p : ℤ)⟩
    (fun c : BivariantClass δ f (p : ℤ) ↦
      (BivariantClass.pushforwardToTarget δ f (p : ℤ) c :
          ChowCohomology.degree δ X.hom p) =
        ChernClass.Derived.newtonClass δ X.hom classes E perfect sit.isDefined p)

/-- Proper pushforward of `newtonClass` recovers the ambient Newton class. -/
theorem newtonClass_spec
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E)) (finiteness : TechnicalCondition X E)
    (p : ℕ) :
    (BivariantClass.pushforwardToTarget δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ)
        (newtonClass i classes E perfect vanishing finiteness p) :
      ChowCohomology.degree δ X.hom p) =
      ChernClass.Derived.newtonClass δ X.hom classes E perfect
        ({ perfect := perfect, offCenter := vanishing, finiteness := finiteness } :
          Situation S δ X i E p RestrictionBehavior.vanishing).isDefined p := sorry

/-- The selected localized Chern class of `E` along `Z ⟶ X` in degree `p`, specified by
proper pushforward to the ambient Chern class. -/
noncomputable def chernClass
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E) (p : ℕ)
    (rankBound : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      (restrictAway i E) 0 p) (finiteness : TechnicalCondition X E) :
    BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ) :=
  let f : Over.mk (i ≫ X.hom) ⟶ X := Over.homMk i
  let sit : Situation S δ X i E p RestrictionBehavior.rankBound :=
    { perfect := perfect, offCenter := rankBound, finiteness := finiteness }
  @Classical.epsilon (BivariantClass δ f (p : ℤ))
    ⟨BivariantClass.pointwiseZero δ f (p : ℤ)⟩
    (fun c : BivariantClass δ f (p : ℤ) ↦
      (BivariantClass.pushforwardToTarget δ f (p : ℤ) c :
          ChowCohomology.degree δ X.hom p) =
        ChernClass.Derived.totalClass δ X.hom classes E perfect sit.isDefined p)

/-- Proper pushforward of `chernClass` recovers the ambient Chern class. -/
theorem chernClass_spec
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E) (p : ℕ)
    (rankBound : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      (restrictAway i E) 0 p) (finiteness : TechnicalCondition X E) :
    (BivariantClass.pushforwardToTarget δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ)
        (chernClass i classes E perfect p rankBound finiteness) :
      ChowCohomology.degree δ X.hom p) =
      ChernClass.Derived.totalClass δ X.hom classes E perfect
        ({ perfect := perfect, offCenter := rankBound, finiteness := finiteness } :
          Situation S δ X i E p RestrictionBehavior.rankBound).isDefined p := sorry

/-- File-local additive structure on homogeneous bivariant classes. -/
-- Local instance justification (instance diamond): Lemma_42_35_4_Additive.instAddCommGroup cannot be imported with Lemma_42_35_3_Vanishing (duplicate zeroClass); a global pointwiseAddCommGroup instance diamonds with ChowCohomology.instAddCommGroupDegree.
local instance bivariantClassAddCommGroup
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) (p : ℤ) : AddCommGroup (BivariantClass δ f p) :=
  BivariantClass.pointwiseAddCommGroup δ f p

section

variable {S : Scheme.{u}} [UniversallyCatenary S]
variable {δ : S → ℤ} [IsDimensionFunction δ]
variable {X : Over S} [LocallyOfFiniteType X.hom]
variable {Z : Scheme.{u}}
variable (i : Z ⟶ X.left) [IsClosedImmersion i]
variable (classes : ChernClass.Theory δ X.hom)
variable (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
variable (perfect : RingedSpace.ModuleDerived.IsPerfect E)
variable (vanishing : IsZero (restrictAway i E))
variable (finiteness : TechnicalCondition X E)

/-- Lemma 42.52.1 (1): in Situation 42.50.1, if `E` vanishes on the complement of `Z`,
then the localized Newton class `P 1 (Z ⟶ X, E)` equals the localized Chern class
`c 1 (Z ⟶ X, E)`. Products of higher-degree formulas are taken in `A⁽¹⁾(Z ⟶ X)`
via `BivariantClass.Cutoff.relativeMul` as in Remark 42.34.7. -/
@[stacks 0FBA]
theorem newtonClass_one :
    newtonClass i classes E perfect vanishing finiteness 1 =
      chernClass i classes E perfect 1
        (rankBound_of_isZero vanishing (Nat.succ_pos 0)) finiteness := sorry

/-- Lemma 42.52.1 (2): in Situation 42.50.1, if `E` vanishes on the complement of `Z`,
then `P 2 (Z ⟶ X, E) = c 1 (Z ⟶ X, E)^2 - 2 • c 2 (Z ⟶ X, E)` in `A⁽¹⁾(Z ⟶ X)`,
with relative multiplication as in Remark 42.34.7. -/
@[stacks 0FBA]
theorem newtonClass_two :
    newtonClass i classes E perfect vanishing finiteness 2 =
      BivariantClass.Cutoff.relativeMul δ
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 1 1
          (chernClass i classes E perfect 1
            (rankBound_of_isZero vanishing (Nat.succ_pos 0)) finiteness)
          (chernClass i classes E perfect 1
            (rankBound_of_isZero vanishing (Nat.succ_pos 0)) finiteness) -
        2 • chernClass i classes E perfect 2
          (rankBound_of_isZero vanishing (Nat.succ_pos 1)) finiteness := sorry

/-- Lemma 42.52.1 (3): in Situation 42.50.1, if `E` vanishes on the complement of `Z`,
then `P 3 (Z ⟶ X, E) = c 1 (Z ⟶ X, E)^3 - 3 • (c 1 (Z ⟶ X, E) * c 2 (Z ⟶ X, E)) +
3 • c 3 (Z ⟶ X, E)` in `A⁽¹⁾(Z ⟶ X)`, with relative multiplication as in
Remark 42.34.7. -/
@[stacks 0FBA]
theorem newtonClass_three :
    newtonClass i classes E perfect vanishing finiteness 3 =
      BivariantClass.Cutoff.relativeMul δ
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 2 1
          (BivariantClass.Cutoff.relativeMul δ
            (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 1 1
            (chernClass i classes E perfect 1
              (rankBound_of_isZero vanishing (Nat.succ_pos 0)) finiteness)
            (chernClass i classes E perfect 1
              (rankBound_of_isZero vanishing (Nat.succ_pos 0)) finiteness))
          (chernClass i classes E perfect 1
            (rankBound_of_isZero vanishing (Nat.succ_pos 0)) finiteness) -
        3 • BivariantClass.Cutoff.relativeMul δ
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 1 2
          (chernClass i classes E perfect 1
            (rankBound_of_isZero vanishing (Nat.succ_pos 0)) finiteness)
          (chernClass i classes E perfect 2
            (rankBound_of_isZero vanishing (Nat.succ_pos 1)) finiteness) +
        3 • chernClass i classes E perfect 3
          (rankBound_of_isZero vanishing (Nat.succ_pos 2)) finiteness := sorry

/-- Lemma 42.52.1 (4): in Situation 42.50.1, if `E` vanishes on the complement of `Z`,
the localized Newton classes satisfy the usual integral Newton recurrence in the
localized Chern classes, with products in `A⁽¹⁾(Z ⟶ X)` as in Remark 42.34.7. -/
@[stacks 0FBA]
theorem newtonClass_succ (n : ℕ) :
    newtonClass i classes E perfect vanishing finiteness (n + 1) =
      (∑ j : Finset.range n,
        ((-1 : ℤ) ^ j.1) •
          BivariantClass.Nonnegative.castGrading δ
            (newtonClass_succ_degree n j.1 j.2)
            (BivariantClass.Cutoff.relativeMul δ
              (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
              ((j.1 + 1 : ℕ) : ℤ) ((n - j.1 : ℕ) : ℤ)
              (chernClass i classes E perfect (j.1 + 1)
                (rankBound_of_isZero vanishing (Nat.succ_pos j.1)) finiteness)
              (newtonClass i classes E perfect vanishing finiteness
                (n - j.1)))) +
        (((-1 : ℤ) ^ n * (n + 1 : ℕ)) •
          chernClass i classes E perfect (n + 1)
            (rankBound_of_isZero vanishing (Nat.succ_pos n)) finiteness) := sorry

end

end AlgebraicGeometry.LocalizedChern
