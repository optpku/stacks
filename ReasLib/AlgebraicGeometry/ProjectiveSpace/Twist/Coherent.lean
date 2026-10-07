module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Tensor

/-!
# Coherence of twists on standard projective space

This leaf records coherence of the canonical twist of a coherent module on
standard projective space over a field.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- The canonical twist of a coherent module on projective space over a field is coherent. -/
instance instIsCoherentTwist
    (k : Type u) [Field k] (n : ℕ)
    (ℱ : (scheme k n).Modules) [ℱ.IsCoherent] (d : ℤ) :
    (twist k n ℱ d).IsCoherent := sorry

end AlgebraicGeometry.ProjectiveSpace
