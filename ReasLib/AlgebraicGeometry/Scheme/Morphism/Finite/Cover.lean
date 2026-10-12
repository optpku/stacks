/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A scheme morphism is finite exactly when some affine open cover of the target has affine
preimages and induces finite maps on global sections. -/
theorem isFinite_iff_exists_affineOpenCover :
    IsFinite f ↔
      ∃ 𝒰 : S.AffineOpenCover.{u},
        ∀ i : 𝒰.I₀,
          IsAffine (f ⁻¹ᵁ (𝒰.f i).opensRange) ∧
            (CommRingCat.Hom.hom
              (Scheme.Hom.appTop (f ∣_ (𝒰.f i).opensRange))).Finite := sorry

/-- A scheme morphism is finite exactly when it is finite after restriction along every member
of some open cover of the target. -/
theorem isFinite_iff_exists_openCover :
    IsFinite f ↔
      ∃ 𝒰 : S.OpenCover.{u},
        ∀ i : 𝒰.I₀, IsFinite (f ∣_ (𝒰.f i).opensRange) := sorry

end AlgebraicGeometry
