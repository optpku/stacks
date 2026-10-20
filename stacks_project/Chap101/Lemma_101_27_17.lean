module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Fppf
import StacksCheckRecall

/-!
# Cancellation of separatedness along an fppf universally injective morphism

If `X ⟶ Y` is surjective, flat, locally of finite presentation, and
universally injective, and if `X ⟶ Z` is separated, then `Y ⟶ Z` is
separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Separated

/- Lemma 101.27.17: Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic
stacks. If `f` is surjective, flat, locally of finite presentation, and
universally injective, and if `f ≫ g` is separated, then `g` is separated. -/
@[stacks 0CPQ] #check
  (AlgebraicGeometry.AlgebraicStack.Separated.of_comp_of_fppf_universallyInjective :
    ∀ {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (f : X ⟶ Y) (g : Y ⟶ Z) [Surjective f] [Flat f]
    [LocallyOfFinitePresentation f] [UniversallyInjective f]
    [Separated (f ≫ g)], Separated g)

end AlgebraicGeometry.AlgebraicStack.Separated
