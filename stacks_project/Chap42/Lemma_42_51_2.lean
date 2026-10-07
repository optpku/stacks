module

import StacksCheckRecall
public import stacks_project.Chap42.Definition_42_50_3_LocalizedClasses

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern.ClassConstruction

/-- Lemma 42.51.2 (1): the class at zero obtained from vanishing deformation data
agrees with the canonical localized Newton class. -/
@[stacks 0FE8]
theorem result_eq_newtonClass
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (F : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect F)
    (vanishing : IsZero (restrictAway i F)) (finiteness : TechnicalCondition X F)
    (p : ℕ)
    (construction : ClassConstruction δ i classes F p .vanishing
      (Situation.vanishing perfect vanishing finiteness))
    (restrictionOnT : RestrictionCondition
      (construction.t ≫
        (BivariantClass.GysinAtInfinity.infinityInclusion X construction.b).left)
      construction.Q p .vanishing)
    (qFiniteness : TechnicalCondition
      (BivariantClass.GysinAtInfinity.compactification X construction.b) construction.Q) :
    construction.result =
      newtonClass i classes F perfect vanishing finiteness p := sorry

/-- Lemma 42.51.2 (2): the class at zero obtained from rank-bounded deformation data
agrees with the canonical localized Chern class. -/
@[stacks 0FE8]
theorem result_eq_chernClass
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (F : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect F) (p : ℕ)
    (rankBound : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      (restrictAway i F) 0 p) (finiteness : TechnicalCondition X F)
    (construction : ClassConstruction δ i classes F p .rankBound
      (Situation.rankBound perfect rankBound finiteness))
    (restrictionOnT : RestrictionCondition
      (construction.t ≫
        (BivariantClass.GysinAtInfinity.infinityInclusion X construction.b).left)
      construction.Q p .rankBound)
    (qFiniteness : TechnicalCondition
      (BivariantClass.GysinAtInfinity.compactification X construction.b) construction.Q) :
    construction.result =
      chernClass i classes F perfect p rankBound finiteness := sorry

end AlgebraicGeometry.LocalizedChern.ClassConstruction
