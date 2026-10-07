module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleSquare
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A local complete-intersection morphism cancels after smooth postcomposition. -/
theorem isLocalCompleteIntersection_of_smooth_of_comp
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : etaleLocally (fun _ _ morphism => AlgebraicGeometry.Smooth morphism) g)
    (hfg : IsLocalCompleteIntersection (f ≫ g)) :
    IsLocalCompleteIntersection f := sorry

/-- Local complete-intersection morphisms have the postcomposition cancellation
property with respect to smooth morphisms. -/
instance instLciHasOfPostcompPropertySmooth {S : Scheme.{u}} :
    MorphismProperty.HasOfPostcompProperty
      (@IsLocalCompleteIntersection S)
      (@etaleLocally S (fun _ _ morphism => AlgebraicGeometry.Smooth morphism)) := sorry

end AlgebraicGeometry.AlgebraicSpace
