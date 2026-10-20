module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- For a finite morphism of schemes, an invertible module becomes trivial over the inverse
image of some open neighborhood of any target point. -/
theorem exists_open_neighborhood_isTrivial_pullback_of_isFinite
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] (y : Y) :
    ∃ V : Y.Opens, y ∈ V ∧
      RingedSpace.IsTrivial
        ((Scheme.Modules.pullback (X.ofRestrict (π ⁻¹ᵁ V).isOpenEmbedding)).obj ℒ) := sorry

end AlgebraicGeometry.Scheme
