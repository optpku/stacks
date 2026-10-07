module

public import ReasLib.AlgebraicGeometry.AffineTriangle.Scheme
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard

/-!
# The Picard group of the affine triangle
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry

namespace AlgebraicGeometry.AffineTriangle

/-- For every field `k`, the Picard group of the affine triangle is additively
equivalent to the multiplicative group of units of `k`. -/
theorem picardGroup_addEquiv (k : Type u) [Field k] :
    Nonempty ((scheme k).PicardGroup ≃+ Additive kˣ) := sorry

end AlgebraicGeometry.AffineTriangle
