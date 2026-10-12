/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Triangulated

/-!
# Mapping-Cone Triangles in the Triangulated DG Homotopy Category

This leaf records the reusable two-out-of-three API for the intrinsic mapping-cone triangles of
right differential graded modules.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory DifferentialGradedCategory

namespace DifferentialGradedModule.MappingCone

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra R}
variable {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, v} A}
variable {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂}

/-- Lemma 22.9.3 (09KE): a morphism of intrinsic mapping-cone triangles whose first two
components are isomorphisms has an isomorphism as its third component. -/
@[stacks 09KE]
theorem triangleK_isIso₃_of_isIso₁₂ (φ : triangleK f₁ ⟶ triangleK f₂)
    [IsIso φ.hom₁] [IsIso φ.hom₂] :
    IsIso φ.hom₃ := sorry

end DifferentialGradedModule.MappingCone
