/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Admissible.Octahedron
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R}
variable {K L M : DifferentialGradedModule.{u, v} A}
variable (alpha : K ⟶ L) (beta : L ⟶ M)
variable (h_alpha : DifferentialGradedModule.IsAdmissibleMono alpha)
variable (h_beta : DifferentialGradedModule.IsAdmissibleMono beta)

/- Lemma 22.10.2 (09KI): two admissibly monic maps of right DG modules have associated
distinguished cone triangles which form an octahedron in the intrinsic DG homotopy category. -/
@[stacks 09KI]
#check (DifferentialGradedModule.MappingCone.nonemptyOctahedron_of_admissibleMono
    alpha beta h_alpha h_beta :
  Nonempty (DifferentialGradedModule.MappingCone.AssociatedOctahedron alpha beta))

/- TR4 for the canonical mapping-cone triangles is available without admissibility assumptions. -/
#check @DifferentialGradedModule.MappingCone.nonemptyOctahedron

/- The three cone triangles are tied back to admissible associated rows by the reusable bridge
API. -/
#check @DifferentialGradedModule.ShortComplex.hasAssociatedConeRow_of_admissibleMono
#check @DifferentialGradedModule.MappingCone.hasAssociatedConeRow_comp_of_admissibleMono
