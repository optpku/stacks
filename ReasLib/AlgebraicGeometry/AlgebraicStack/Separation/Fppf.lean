module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-!
# Cancellation of separatedness along fppf universally injective morphisms
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Separated

/-- For composable morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic
stacks, if `f` is surjective, flat, locally of finite presentation, and
universally injective, and if `f ≫ g` is separated, then `g` is separated. -/
theorem of_comp_of_fppf_universallyInjective {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (f : X ⟶ Y) (g : Y ⟶ Z) [Surjective f] [Flat f]
    [LocallyOfFinitePresentation f] [UniversallyInjective f]
    [Separated (f ≫ g)] : Separated g :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Separated
