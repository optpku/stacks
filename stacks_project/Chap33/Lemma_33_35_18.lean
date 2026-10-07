module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Regularity.KernelBound

@[expose] public section

open CategoryTheory

universe u

/-
Lemma 33.35.18: for fixed `n`, positive `r`, and `P ∈ ℚ[t]`, there is an integer `m`
such that over every field, the coherent kernel of any short exact presentation of a coherent
sheaf with Hilbert polynomial `P` by the standard rank-`r` finite-free sheaf on projective
`n`-space is `m`-regular.
-/
@[stacks 08AG] #check
  (AlgebraicGeometry.ProjectiveSpace.exists_kernel_isMRegular_bound_of_isHilbertPolynomial :
    ∀ (n r : ℕ) (_ : 1 ≤ r) (P : Polynomial ℚ),
      ∃ m : ℤ,
        ∀ (k : Type u) [Field k]
          (𝒦 ℱ : (AlgebraicGeometry.ProjectiveSpace.scheme k n).Modules)
          [𝒦.IsCoherent] [ℱ.IsCoherent],
          AlgebraicGeometry.ProjectiveSpace.IsHilbertPolynomial k n ℱ P →
            ∀ (ι : 𝒦 ⟶
                (SheafOfModules.freeFin r :
                  (AlgebraicGeometry.ProjectiveSpace.scheme k n).Modules))
              (π : (SheafOfModules.freeFin r :
                  (AlgebraicGeometry.ProjectiveSpace.scheme k n).Modules) ⟶ ℱ)
              (hιπ : ι ≫ π = 0),
              (ShortComplex.mk ι π hιπ).ShortExact →
                AlgebraicGeometry.ProjectiveSpace.IsMRegular k n 𝒦 m)
