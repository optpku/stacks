/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.InfinitesimalNeighbourhoodCohomology
public import ReasLib.AlgebraicGeometry.Scheme.Variety
public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ZeroScheme
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.InfinitesimalNeighbourhoodCohomology

/-- For a proper Cohen–Macaulay surface over a field, the degree-zero cohomology comparison
for a finite locally free module along the infinitesimal neighbourhoods of the zero scheme
of a regular section of an ample invertible module is an isomorphism. -/
public theorem comparison_isIso_of_cohenMacaulay_surface
    {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    [Variety P] (L : P.left.Modules) [L.Invertible] [L.IsAmple]
    (s : L.sections) [RingedSpace.IsRegularSection L s]
    (E : P.left.Modules) [E.IsFiniteLocallyFree] [CohenMacaulay P.left]
    [h_dimension : Fact (topologicalKrullDim P.left = 2)] :
    IsIso (comparison P L s E 0) := sorry

/-- For a proper Cohen–Macaulay threefold over a field, the degree-zero cohomology comparison
for a finite locally free module along the infinitesimal neighbourhoods of the zero scheme
of a regular section of an ample invertible module is an isomorphism. -/
public theorem comparison_isIso_of_cohenMacaulay_threefold_degree_zero
    {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    [Variety P] (L : P.left.Modules) [L.Invertible] [L.IsAmple]
    (s : L.sections) [RingedSpace.IsRegularSection L s]
    (E : P.left.Modules) [E.IsFiniteLocallyFree] [CohenMacaulay P.left]
    [h_dimension : Fact (topologicalKrullDim P.left = 3)] :
    IsIso (comparison P L s E 0) := sorry

/-- For a proper Cohen–Macaulay threefold over a field, the degree-one cohomology comparison
for a finite locally free module along the infinitesimal neighbourhoods of the zero scheme
of a regular section of an ample invertible module is an isomorphism. -/
public theorem comparison_isIso_of_cohenMacaulay_threefold_degree_one
    {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    [Variety P] (L : P.left.Modules) [L.Invertible] [L.IsAmple]
    (s : L.sections) [RingedSpace.IsRegularSection L s]
    (E : P.left.Modules) [E.IsFiniteLocallyFree] [CohenMacaulay P.left]
    [h_dimension : Fact (topologicalKrullDim P.left = 3)] :
    IsIso (comparison P L s E 1) := sorry

/-- For a proper normal threefold over a field, the degree-zero cohomology comparison
for a finite locally free module along the infinitesimal neighbourhoods of the zero scheme
of a regular section of an ample invertible module is an isomorphism. -/
public theorem comparison_isIso_of_normal_threefold_degree_zero
    {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    [Variety P] (L : P.left.Modules) [L.Invertible] [L.IsAmple]
    (s : L.sections) [RingedSpace.IsRegularSection L s]
    (E : P.left.Modules) [E.IsFiniteLocallyFree]
    [h_normal : Fact P.left.isNormal]
    [h_dimension : Fact (topologicalKrullDim P.left = 3)] :
    IsIso (comparison P L s E 0) := sorry

end AlgebraicGeometry.Scheme.InfinitesimalNeighbourhoodCohomology
