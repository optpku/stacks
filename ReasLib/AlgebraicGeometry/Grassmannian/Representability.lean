module

public import Mathlib.CategoryTheory.RepresentedBy
public import ReasLib.AlgebraicGeometry.Grassmannian.Functor

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Grassmannian

/-- The Grassmannian functor of rank-`n - k` locally free quotients of the free rank-`n`
module sheaf is representable when `0 < k < n`. -/
theorem functor_isRepresentable (k n : ℕ) (hk : 0 < k) (hkn : k < n) :
    Functor.IsRepresentable (functor k n) := sorry

end AlgebraicGeometry.Grassmannian
