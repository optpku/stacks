module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Perfect.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Perfect.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Section

/-!
# Perfect morphisms over smooth morphisms

Perfect scheme morphisms can be cancelled after postcomposition with a smooth morphism.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyOfType

/-- Perfect scheme morphisms can be cancelled after postcomposition with a smooth
scheme morphism. -/
instance instIsPerfectRingMapHasOfPostcompPropertySmooth :
    MorphismProperty.HasOfPostcompProperty
      (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsPerfectRingMap)
      (@AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) := sorry

/-- If `g` is smooth and `f ≫ g` is a perfect scheme morphism, then `f` is perfect. -/
theorem isPerfectRingMap_of_smooth_of_comp
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [Smooth g]
    [LocallyOfType RingHom.IsPerfectRingMap (f ≫ g)] :
    LocallyOfType RingHom.IsPerfectRingMap f := sorry

end AlgebraicGeometry.LocallyOfType
