module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Two-out-of-three for mapping-cone triangles

The generic two-out-of-three theorem is owned by `Pretriangulated`.  This leaf records the
mapping-cone specialization used throughout homotopy-category arguments, without introducing a
new triangle wrapper.
-/

open CategoryTheory CategoryTheory.Pretriangulated
open CochainComplex HomotopyCategory

universe v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Limits.HasZeroObject 𝒜] [Preadditive 𝒜]
  [Limits.HasBinaryBiproducts 𝒜]
variable {K₁ L₁ K₂ L₂ : CochainComplex 𝒜 ℤ}
variable {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂}

/-- Lemma 13.9.13: a morphism of standard mapping-cone triangles whose first two components are
isomorphisms has an isomorphism as its third component. -/
@[stacks 014K "mapping-cone triangle two-out-of-three"]
theorem mappingCone_triangleh_isIso₃_of_isIso₁₂
    (φ : mappingCone.triangleh f₁ ⟶ mappingCone.triangleh f₂)
    [IsIso φ.hom₁] [IsIso φ.hom₂] :
    IsIso φ.hom₃ := sorry

end CategoryTheory
