/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.InfinitesimalNeighbourhoodCohomology

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

open Hom

/-- The source-facing tower is represented by the ambient tower and its stage isomorphisms. -/
abbrev infinitesimalNeighbourhoodSourceCohomologySystem
    {k : Type u} [Field k] (P : SchemeOverField k)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules) (i : ℕ) : SequentialInverseSystem (ModuleCat k) :=
  InfinitesimalNeighbourhoodCohomology.system P L s F i

/-- The source-facing comparison, viewed through the canonical stage identifications. -/
noncomputable abbrev infinitesimalNeighbourhoodSourceCohomologyComparison
    {k : Type u} [Field k] (P : SchemeOverField k)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules) (i : ℕ) :
    cohomology P.hom F i ⟶ limit (infinitesimalNeighbourhoodSourceCohomologySystem P L s F i) :=
  InfinitesimalNeighbourhoodCohomology.comparison P L s F i

end AlgebraicGeometry.Scheme
