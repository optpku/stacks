module

public import stacks_project.Chap42.Definition_42_50_3_RationalBivariant
public import stacks_project.Chap42.Lemma_42_49_3_AtZero
public import stacks_project.Chap42.Lemma_42_50_2
public import ReasLib.AlgebraicGeometry.LocalizedChern.GlobalProducer

public import ReasLib.AlgebraicGeometry.LocalizedChern.Classes
public import ReasLib.AlgebraicGeometry.Scheme.Over.ClosedImmersion

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- The localized Chern character with degree-`p` component `Pₚ(Z ⟶ X, E) / p!`. -/
def character
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E)) (finiteness : TechnicalCondition X E) :
    BivariantClass.Nonnegative.RationalCompletion δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) :=
  fun p ↦ TensorProduct.tmul ℤ
    (newtonClass i classes E perfect vanishing finiteness p) ((p.factorial : ℚ)⁻¹)

/-- Evaluation of the localized Chern character gives `Pₚ(Z ⟶ X, E) / p!`. -/
theorem character_apply
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E)) (finiteness : TechnicalCondition X E)
    (p : ℕ) :
    character i classes E perfect vanishing finiteness p =
      TensorProduct.tmul ℤ (newtonClass i classes E perfect vanishing finiteness p)
        ((p.factorial : ℚ)⁻¹) := rfl

/-- Componentwise rationalization identifies the localized Chern character with
the character in the explicit pointwise tensor representation. -/
theorem character_toCanonical
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E)) (finiteness : TechnicalCondition X E) :
    (fun p ↦ BivariantClass.Nonnegative.canonicalDegreeEquiv δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p
      (character i classes E perfect vanishing finiteness p)) =
        rationalCharacter i classes E perfect vanishing finiteness := by
  funext p
  exact BivariantClass.Nonnegative.canonicalDegreeEquiv_tmul δ
    (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p
    (newtonClass i classes E perfect vanishing finiteness p) ((p.factorial : ℚ)⁻¹)

/- Compatibility: the shared localized Newton class. -/
#check (AlgebraicGeometry.LocalizedChern.newtonClass :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E)) (finiteness : TechnicalCondition X E)
    (p : ℕ),
    BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ))

/- Compatibility: the localized Chern character in the inferred tensor representation. -/
#check (AlgebraicGeometry.LocalizedChern.character :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E)) (finiteness : TechnicalCondition X E),
    BivariantClass.Nonnegative.RationalCompletion δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))

/- Compatibility: the shared localized Chern class. -/
#check (AlgebraicGeometry.LocalizedChern.chernClass :
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
