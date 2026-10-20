module

public import ReasLib.AlgebraicGeometry.LocalizedChern.Definedness

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- A localized-Chern situation has defined ambient derived Chern classes. -/
#check (AlgebraicGeometry.LocalizedChern.Situation.isDefined :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom]
    {Z : Scheme.{u}} {i : Z ⟶ X.left}
    [IsClosedImmersion i]
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    {mode : LocalizedChern.RestrictionBehavior}
    (situation : LocalizedChern.Situation S δ X i E p mode),
    ChernClass.Derived.IsDefined E)
