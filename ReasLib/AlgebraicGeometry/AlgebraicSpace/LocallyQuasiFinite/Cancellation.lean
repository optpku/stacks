module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Cancellation of local quasi-finiteness against arbitrary postcomposition

If a composite morphism of algebraic spaces is locally quasi-finite, then so
is the first factor. No hypothesis is imposed on the second factor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace LocallyQuasiFinite

/-- If a composite morphism of algebraic spaces is locally quasi-finite, then
so is the first factor. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyQuasiFinite (f ≫ g)] : LocallyQuasiFinite f := sorry

end LocallyQuasiFinite

/-- Locally quasi-finite morphisms of algebraic spaces cancel against an
arbitrary postcomposition. -/
instance locallyQuasiFinite_hasOfPostcompProperty {S : Scheme.{u}} :
    MorphismProperty.HasOfPostcompProperty
      (@LocallyQuasiFinite S : MorphismProperty (AlgebraicSpace S)) ⊤ := sorry

end AlgebraicGeometry.AlgebraicSpace
