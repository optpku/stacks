module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace.Projectivization

/-!
# Affineness of projectivization

The canonical projectivization of punctured affine space is an affine morphism.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.PuncturedAffineSpace

variable (A : Type u) [CommRing A] (n : ℕ)

/-- The canonical projectivization `toProjectiveSpace A n` is an affine morphism. -/
instance toProjectiveSpace_isAffineHom : IsAffineHom (toProjectiveSpace A n) := sorry

end AlgebraicGeometry.PuncturedAffineSpace
