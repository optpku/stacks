module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials.Transitivity
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth
import Mathlib.Tactic.CrossRefAttribute

/-!
# Transitivity of differentials for formally smooth scheme morphisms

For composable scheme morphisms `X ⟶ Y ⟶ S`, formal smoothness of `X ⟶ Y` makes
the canonical transitivity complex of relative differentials short exact.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FormallySmooth

/-- If `f : X ⟶ Y` is formally smooth, then the canonical transitivity complex

`f^* Ω[Y/S] ⟶ Ω[X/S] ⟶ Ω[X/Y]`

is short exact. -/
@[stacks 06B6]
theorem relativeDifferentialsTransitivity_shortExact
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [FormallySmooth f] :
    (RingedSpace.Hom.Differentials.Transitivity.complex
      f.toShHom g.toShHom).ShortExact := sorry

end AlgebraicGeometry.FormallySmooth
