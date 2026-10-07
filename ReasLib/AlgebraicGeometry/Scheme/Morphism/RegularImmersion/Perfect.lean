module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Implications
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Noetherian
public import ReasLib.RingTheory.Ideal.Regularity.ProjectiveDimension
public import ReasLib.RingTheory.Ideal.Regularity.TorDimension
public import ReasLib.RingTheory.RingHom.Perfect.Basic

/-!
# Perfectness and regular immersions

Regular and Koszul-regular immersions are perfect. Conversely, a perfect
immersion into a locally Noetherian scheme is regular when its conormal sheaf
is finite locally free.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsKoszulRegularImmersion

/-- A Koszul-regular immersion of schemes is locally of type
`RingHom.IsPerfectRingMap`. -/
@[stacks 068C, instance]
theorem isPerfect
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsKoszulRegularImmersion i] :
    LocallyOfType RingHom.IsPerfectRingMap i := sorry

end AlgebraicGeometry.IsKoszulRegularImmersion

namespace AlgebraicGeometry.IsRegularImmersion

/-- A regular immersion of schemes is locally of type `RingHom.IsPerfectRingMap`. -/
@[stacks 068C]
theorem isPerfect
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsRegularImmersion i] :
    LocallyOfType RingHom.IsPerfectRingMap i := sorry

end AlgebraicGeometry.IsRegularImmersion

namespace AlgebraicGeometry.IsImmersion

/-- A perfect immersion into a locally Noetherian scheme is regular when its
conormal sheaf is finite locally free. -/
@[stacks 0FK1, instance]
theorem isRegular_of_perfect_of_conormal
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsImmersion i]
    [LocallyOfType RingHom.IsPerfectRingMap i] [IsLocallyNoetherian Y]
    [Scheme.Modules.IsFiniteLocallyFree (Scheme.Hom.conormalSheaf i)] :
    IsRegularImmersion i := sorry

end AlgebraicGeometry.IsImmersion

namespace AlgebraicGeometry

/-- If two composable morphisms are immersions, the target is locally Noetherian,
the composite is a regular immersion, and the first morphism is perfect, then
both morphisms are regular immersions. -/
theorem regularImmersion_factors_of_perfect_of_comp
    {X Y Z : Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsLocallyNoetherian X] [IsImmersion i] [IsImmersion j]
    [IsRegularImmersion (i ≫ j)] [LocallyOfType RingHom.IsPerfectRingMap i] :
    IsRegularImmersion i ∧ IsRegularImmersion j := sorry

end AlgebraicGeometry
