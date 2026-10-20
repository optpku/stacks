module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.MappingCone.Triangle
import StacksCheckRecall

@[expose] public section

universe u v w

open CategoryTheory
open scoped DifferentialGradedModule

namespace DifferentialGradedModule.MappingCone

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R}
variable {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, v} A}
variable {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂}
variable {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂}
variable (H : Homotopy (f₁ ≫ b) (a ≫ f₂))

/- Lemma 22.6.2 (09KD): a square of right differential graded `A`-module maps that commutes
up to the specified homotopy `H` induces a morphism between its mapping-cone triangles in
`K(Mod(A, d))`. -/
@[stacks 09KD]
#check (triangleMapKOfHomotopy H : triangleK f₁ ⟶ triangleK f₂)

/- Its third component is represented by the explicit upper-triangular cone map
`(b, H; 0, a)`. -/
#check (triangleMapKOfHomotopy_hom₃ H :
  (triangleMapKOfHomotopy H).hom₃ = (toK A).map (mapOfHomotopy H))

end DifferentialGradedModule.MappingCone
