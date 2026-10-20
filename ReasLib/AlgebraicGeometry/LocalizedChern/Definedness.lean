module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.Definedness
public import ReasLib.AlgebraicGeometry.LocalizedChern.Situation

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocalizedChern.Situation

/-- A localized-Chern situation supplies the hypotheses needed for the ambient derived
Chern classes to be defined. -/
theorem isDefined
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    {i : Z ⟶ X.left} [IsClosedImmersion i]
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    {mode : RestrictionBehavior} (situation : Situation S δ X i E p mode) :
    ChernClass.Derived.IsDefined E := sorry

end AlgebraicGeometry.LocalizedChern.Situation
