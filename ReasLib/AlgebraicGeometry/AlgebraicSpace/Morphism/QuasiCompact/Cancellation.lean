module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Cancellation of quasi-compactness against quasi-separated postcomposition

If a composite morphism of algebraic spaces is quasi-compact and the second
factor is quasi-separated, then the first factor is quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace QuasiCompact

/-- If a composite morphism of algebraic spaces is quasi-compact and the second
factor is quasi-separated, then the first factor is quasi-compact. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact (f ≫ g)] [QuasiSeparated g] : QuasiCompact f := sorry

end QuasiCompact

/-- Quasi-compact morphisms of algebraic spaces cancel against a quasi-separated
postcomposition. -/
instance quasiCompact_hasOfPostcompProperty {S : Scheme.{u}} :
    MorphismProperty.HasOfPostcompProperty
      (@QuasiCompact S : MorphismProperty (AlgebraicSpace S))
      (@QuasiSeparated S) := sorry

end AlgebraicGeometry.AlgebraicSpace
