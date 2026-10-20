module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.LocalizedChern.Classes

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.LocalizedChern

/- Definition 42.50.3 (1): the localized Newton class in the vanishing case. -/
@[stacks 0FB5] #check (AlgebraicGeometry.LocalizedChern.newtonClass :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E)) (finiteness : TechnicalCondition X E)
    (p : ℕ),
    BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ))

/- Definition 42.50.3 (2): the completed localized Chern character, with coefficient Pₚ/p!. -/
@[stacks 0FB5] #check (AlgebraicGeometry.LocalizedChern.rationalCharacter :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E)) (finiteness : TechnicalCondition X E),
    BivariantClass.Nonnegative.Rational.Completion δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))

/- Definition 42.50.3 (3): the localized Chern class in the rank-bound case. -/
@[stacks 0FB5] #check (AlgebraicGeometry.LocalizedChern.chernClass :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E) (p : ℕ)
    (rankBound : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      (restrictAway i E) 0 p) (finiteness : TechnicalCondition X E),
    BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ))

end AlgebraicGeometry.LocalizedChern
