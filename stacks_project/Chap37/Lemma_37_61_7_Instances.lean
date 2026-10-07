module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Perfect

@[expose] public section

open CategoryTheory

universe u

open AlgebraicGeometry

#check (AlgebraicGeometry.IsKoszulRegularImmersion.isPerfect :
  ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsKoszulRegularImmersion i],
    LocallyOfType RingHom.IsPerfectRingMap i)
