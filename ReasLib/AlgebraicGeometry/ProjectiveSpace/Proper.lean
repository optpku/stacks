module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Properness of standard projective space

This leaf owns only the properness instance for the standard affine-base projective-space model.
The core `Proj` construction stays available from `Basic` without importing properness machinery.
Valuative-criterion consequences are consumed from the shared morphism API rather than through a
projective-space-specific wrapper.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- The standard projective-space structure morphism is proper over its affine base. -/
@[stacks 01KG "proper projective-space structure morphism"]
instance toSpec_isProper (R : Type u) [CommRing R] (n : ℕ) :
    IsProper (toSpec R n) := sorry

end AlgebraicGeometry.ProjectiveSpace
