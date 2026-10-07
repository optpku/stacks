module

public import stacks_project.Chap42.Situation_42_50_1_LocalizedChern

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocalizedChern.Situation

/-- Enlarging a closed center preserves either off-center condition in a localized-Chern
situation. -/
theorem enlargeCenter
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z Z' : Scheme.{u}}
    (j : Z ⟶ Z') (i : Z' ⟶ X.left)
    [IsClosedImmersion j] [IsClosedImmersion i]
    {E : RingedSpace.ModuleDerived X.left.toRingedSpace} {p : ℕ}
    {mode : RestrictionBehavior}
    (situation : Situation S δ X (j ≫ i) E p mode) :
    Situation S δ X i E p mode := sorry

end AlgebraicGeometry.LocalizedChern.Situation
