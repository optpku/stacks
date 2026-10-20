module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.HilbertPolynomial
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Regularity

/-!
# Uniform regularity bounds for kernels on projective space

This file records a uniform regularity bound for kernels of finite-free presentations whose
quotients have a fixed Hilbert polynomial.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- For fixed projective dimension, positive rank, and Hilbert polynomial, the kernels of
short exact presentations of coherent sheaves by the standard finite-free sheaf have a
uniform regularity bound over every field. -/
theorem exists_kernel_isMRegular_bound_of_isHilbertPolynomial
    (n r : ℕ) (hr : 1 ≤ r) (P : Polynomial ℚ) :
    ∃ m : ℤ,
      ∀ (k : Type u) [Field k]
        (𝒦 ℱ : (scheme k n).Modules) [𝒦.IsCoherent] [ℱ.IsCoherent],
        IsHilbertPolynomial k n ℱ P →
          ∀ (ι : 𝒦 ⟶ (SheafOfModules.freeFin r : (scheme k n).Modules))
            (π : (SheafOfModules.freeFin r : (scheme k n).Modules) ⟶ ℱ)
            (hιπ : ι ≫ π = 0),
            (ShortComplex.mk ι π hιπ).ShortExact →
              IsMRegular k n 𝒦 m := sorry

end AlgebraicGeometry.ProjectiveSpace
