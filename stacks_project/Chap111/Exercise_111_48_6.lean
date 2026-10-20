module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.SerreDuality

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

universe u

#check (AlgebraicGeometry.ProjectiveSpace.omega_topExt_finrank :
  ∀ {k : Type u} [Field k] (d : ℕ) [HasExt (AlgebraicGeometry.ProjectiveSpace.scheme k d).Modules],
    Module.finrank k
      (Ext (𝟙_ (AlgebraicGeometry.ProjectiveSpace.scheme k d).Modules)
        (AlgebraicGeometry.ProjectiveSpace.omega k d) d) = 1)

/- Exercise 111.48.6
For finite locally free modules on projective space over a field, cup product followed by
trace gives a perfect pairing in complementary degrees. Ext from the tensor unit represents
cohomology; the preceding rank-one assertion supplies the basis-free identification of the
top cohomology of the dualizing twist with k.
-/
@[stacks 0DD6] #check (AlgebraicGeometry.ProjectiveSpace.extCupProduct_trace_nondegenerate :
  ∀ {k : Type u} [Field k] (d i : ℕ) (hi : i ≤ d)
    (E F : (AlgebraicGeometry.ProjectiveSpace.scheme k d).Modules)
    [IsFiniteLocallyFree E] [IsFiniteLocallyFree F]
    [HasExt (AlgebraicGeometry.ProjectiveSpace.scheme k d).Modules],
    Function.Bijective (AlgebraicGeometry.ProjectiveSpace.extCupProductTracePairing E F i hi) ∧
      Function.Bijective (AlgebraicGeometry.ProjectiveSpace.extCupProductTracePairing E F i hi).flip)
