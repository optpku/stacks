/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.InfinitesimalNeighbourhoodCohomology.SpecialCases
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

public section

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.InfinitesimalNeighbourhoodCohomology

/- Example 52.28.3 (1): the comparison is an isomorphism in degree zero for a
proper Cohen–Macaulay surface with an ample effective Cartier divisor and finite
locally free coefficients. -/
@[stacks 0EL3] #check (AlgebraicGeometry.Scheme.InfinitesimalNeighbourhoodCohomology.comparison_isIso_of_cohenMacaulay_surface :
    ∀ {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    [Variety P] (L : P.left.Modules) [L.Invertible] [L.IsAmple]
    (s : L.sections) [RingedSpace.IsRegularSection L s]
    (E : P.left.Modules) [E.IsFiniteLocallyFree] [CohenMacaulay P.left]
    [h_dimension : Fact (topologicalKrullDim P.left = 2)],
    IsIso (comparison P L s E 0))

/- Example 52.28.3 (2): the comparison is an isomorphism in degree zero for a
proper Cohen–Macaulay threefold with an ample effective Cartier divisor and finite
locally free coefficients. -/
@[stacks 0EL3] #check (AlgebraicGeometry.Scheme.InfinitesimalNeighbourhoodCohomology.comparison_isIso_of_cohenMacaulay_threefold_degree_zero :
    ∀ {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    [Variety P] (L : P.left.Modules) [L.Invertible] [L.IsAmple]
    (s : L.sections) [RingedSpace.IsRegularSection L s]
    (E : P.left.Modules) [E.IsFiniteLocallyFree] [CohenMacaulay P.left]
    [h_dimension : Fact (topologicalKrullDim P.left = 3)],
    IsIso (comparison P L s E 0))

/- Example 52.28.3 (3): the comparison is an isomorphism in degree one for a
proper Cohen–Macaulay threefold with an ample effective Cartier divisor and finite
locally free coefficients. -/
@[stacks 0EL3] #check (AlgebraicGeometry.Scheme.InfinitesimalNeighbourhoodCohomology.comparison_isIso_of_cohenMacaulay_threefold_degree_one :
    ∀ {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    [Variety P] (L : P.left.Modules) [L.Invertible] [L.IsAmple]
    (s : L.sections) [RingedSpace.IsRegularSection L s]
    (E : P.left.Modules) [E.IsFiniteLocallyFree] [CohenMacaulay P.left]
    [h_dimension : Fact (topologicalKrullDim P.left = 3)],
    IsIso (comparison P L s E 1))

/- Example 52.28.3 (4): for a proper normal threefold with an ample effective
Cartier divisor and finite locally free coefficients, the comparison is an
isomorphism in degree zero; no degree-one isomorphism is asserted. -/
@[stacks 0EL3] #check (AlgebraicGeometry.Scheme.InfinitesimalNeighbourhoodCohomology.comparison_isIso_of_normal_threefold_degree_zero :
    ∀ {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    [Variety P] (L : P.left.Modules) [L.Invertible] [L.IsAmple]
    (s : L.sections) [RingedSpace.IsRegularSection L s]
    (E : P.left.Modules) [E.IsFiniteLocallyFree]
    [h_normal : Fact P.left.isNormal]
    [h_dimension : Fact (topologicalKrullDim P.left = 3)],
    IsIso (comparison P L s E 0))

end AlgebraicGeometry.Scheme.InfinitesimalNeighbourhoodCohomology
