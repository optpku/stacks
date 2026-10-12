/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.MappingCone
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R}
variable {K L : DifferentialGradedModule.{u, v} A} (f : K ⟶ L)

/- Definition 22.6.1 (09KA): the cone of `f : K ⟶ L` is the right differential graded
`A`-module with degree-`n` term `L.X n × K.X (n + 1)` and differential
`(d_L, f; 0, -d_K)`. -/
@[stacks 09KA]
#check (mappingCone f : DifferentialGradedModule A)

/- The canonical map `i : L ⟶ mappingCone f` is the inclusion of the first summand. -/
#check (MappingCone.inclusion f : L ⟶ mappingCone f)

/- The canonical map `p : mappingCone f ⟶ K[1]` is the projection to the shifted source. -/
#check (MappingCone.projection f : mappingCone f ⟶ shift K 1)

/- The underlying complex agrees canonically with Mathlib's mapping-cone construction. -/
#check (mappingConeToCochainMappingCone f :
  (mappingCone f).toCochainComplex ≅
    CochainComplex.mappingCone (Hom.toCochainMap f))

end DifferentialGradedModule
