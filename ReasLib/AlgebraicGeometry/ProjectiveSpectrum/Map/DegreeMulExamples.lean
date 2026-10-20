module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.DegreeMul
public import ReasLib.RingTheory.MvPolynomial.StandardGrading

/-! # Coordinate inclusions and proper domains on projective spectra -/

@[expose] public section

namespace AlgebraicGeometry

/-- The coordinate inclusion from the standard-graded one-variable integer polynomial ring
into the standard-graded two-variable integer polynomial ring preserves degrees. -/
noncomputable def coordinateRename :
    DegreeMulHom (MvPolynomial.standardGrading (Fin 1) ℤ)
      (MvPolynomial.standardGrading (Fin 2) ℤ) 1 :=
  DegreeMulHom.ofRingHom
    (MvPolynomial.rename (Fin.castSucc : Fin 1 → Fin 2)).toRingHom
    (Nat.le_refl 1) (fun {d} {x} hx ↦ by
      change (MvPolynomial.rename (Fin.castSucc : Fin 1 → Fin 2) x).IsHomogeneous (d * 1)
      rw [Nat.mul_one]
      exact MvPolynomial.IsHomogeneous.rename_isHomogeneous hx)

/-- The coordinate inclusion from one variable into two variables has a proper Proj domain. -/
theorem coordinateRename_domain_ne_top :
    DegreeMulHom.domain coordinateRename ≠ ⊤ := sorry

end AlgebraicGeometry
