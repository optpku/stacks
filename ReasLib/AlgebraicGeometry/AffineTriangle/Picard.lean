module

public import ReasLib.AlgebraicGeometry.AffineTriangle.Scheme
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Ring.Units

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

/-- The Picard group of the affine triangle over a field with nontrivial units is nontrivial. -/
instance nontrivial_picardGroup (k : Type u) [Field k] [hUnits : Nontrivial kˣ] :
    Nontrivial (scheme k).PicardGroup := sorry

/-- The affine triangle over the rational numbers is affine and has nontrivial Picard group. -/
theorem rational_isAffine_nontrivial_picardGroup :
    IsAffine (scheme ℚ) ∧ Nontrivial (scheme ℚ).PicardGroup := by
  refine ⟨inferInstance, nontrivial_picardGroup ℚ (hUnits := ?_)⟩
  refine ⟨1, -1, ?_⟩
  intro h
  exact (by decide : (1 : ℚ) ≠ -1) (congrArg (fun a : ℚˣ => (a : ℚ)) h)

end AlgebraicGeometry.AffineTriangle
