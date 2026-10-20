module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Regularity.FieldExtension
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Regularity.HyperplaneSection

/-!
# Monotonicity of projective-space regularity

This file records monotonicity of regularity for coherent module sheaves on standard projective
space.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.IsMRegular

/-- A coherent module sheaf on projective space that is `m`-regular is also `(m + 1)`-regular. -/
theorem add_one
    {k : Type u} [Field k] {n : ℕ} {ℱ : (ProjectiveSpace.scheme k n).Modules} [ℱ.IsCoherent]
    {m : ℤ} (hℱ : IsMRegular k n ℱ m) :
    IsMRegular k n ℱ (m + 1) := sorry

end AlgebraicGeometry.ProjectiveSpace.IsMRegular
