/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Admissible.MappingConeComparison
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Triangulated

/-!
# Octahedra of Differential Graded Module Maps

Mapping-cone triangles give the canonical reusable TR4 presentation in the intrinsic DG
homotopy category.  For admissibly monic maps, companion statements identify all three cone
triangles with triangles associated to admissible short exact sequences.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedModule.MappingCone

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra R}
variable {K L M : DifferentialGradedModule.{u, v} A}

/-- The canonical TR4 data type for the three mapping-cone triangles of two composable
DG-module maps. -/
abbrev ConeOctahedron (alpha : K ⟶ L) (beta : L ⟶ M) :=
  Octahedron
    (Functor.map_comp (toK A) alpha beta).symm
    (Homotopy.mappingCone_triangleK_distinguished A alpha)
    (Homotopy.mappingCone_triangleK_distinguished A beta)
    (Homotopy.mappingCone_triangleK_distinguished A (alpha ≫ beta))

/-- The three standard mapping-cone triangles of two composable DG-module maps form an
octahedron.  This is the canonical assumption-free TR4 interface. -/
theorem nonemptyOctahedron (alpha : K ⟶ L) (beta : L ⟶ M) :
    Nonempty (ConeOctahedron alpha beta) := sorry

/-- The cone triangle of the composite of two admissible monomorphisms is associated to an
admissible short exact sequence. -/
theorem hasAssociatedConeRow_comp_of_admissibleMono
    (alpha : K ⟶ L) (beta : L ⟶ M)
    (h_alpha : DifferentialGradedModule.IsAdmissibleMono alpha)
    (h_beta : DifferentialGradedModule.IsAdmissibleMono beta) :
    ShortComplex.HasAssociatedConeRow (alpha ≫ beta) := sorry

/-- An associated octahedron consists of admissible quotient-row presentations of all three
cone triangles together with the canonical TR4 datum relating those triangles. -/
@[stacks 09KI "associated octahedra of admissible DG-module monomorphisms"]
structure AssociatedOctahedron (alpha : K ⟶ L) (beta : L ⟶ M) where
  /-- An admissible associated row presenting the cone triangle of `alpha`. -/
  row₁₂ : ShortComplex.HasAssociatedConeRow alpha
  /-- An admissible associated row presenting the cone triangle of `alpha ≫ beta`. -/
  row₁₃ : ShortComplex.HasAssociatedConeRow (alpha ≫ beta)
  /-- An admissible associated row presenting the cone triangle of `beta`. -/
  row₂₃ : ShortComplex.HasAssociatedConeRow beta
  /-- The TR4 octahedron on the three canonical cone representatives. -/
  octahedron : ConeOctahedron alpha beta

/-- Lemma 22.10.2 (09KI): if `alpha` and `beta` are admissible monomorphisms of right
DG `A`-modules, their associated distinguished cone triangles satisfy TR4.  The three associated
row witnesses are supplied by `ShortComplex.hasAssociatedConeRow_of_admissibleMono` and
`hasAssociatedConeRow_comp_of_admissibleMono`. -/
@[stacks 09KI]
theorem nonemptyOctahedron_of_admissibleMono
    (alpha : K ⟶ L) (beta : L ⟶ M)
    (h_alpha : DifferentialGradedModule.IsAdmissibleMono alpha)
    (h_beta : DifferentialGradedModule.IsAdmissibleMono beta) :
    Nonempty (AssociatedOctahedron alpha beta) := sorry

end DifferentialGradedModule.MappingCone
