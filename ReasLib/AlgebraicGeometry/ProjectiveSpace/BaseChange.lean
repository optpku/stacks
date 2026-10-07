module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Coordinate
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.Basic
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Projective space over a scheme

Projective space over an arbitrary scheme is obtained by base change from the integral model.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Projective `n`-space over a scheme `S`, obtained by base change from projective `n`-space
over `ℤ`. -/
def ProjectiveSpace (n : ℕ) (S : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from S)
    (terminal.from (ProjectiveSpace.scheme (ULift.{u} ℤ) n))

namespace ProjectiveSpace

/-- The canonical projection from projective `n`-space over `S` to its base scheme `S`. -/
def toBase (n : ℕ) (S : Scheme.{u}) : ProjectiveSpace n S ⟶ S :=
  pullback.fst _ _

/-- Projective `n`-space over `S` is canonically a scheme over `S`. -/
@[simps -isSimp]
instance over (n : ℕ) (S : Scheme.{u}) : (ProjectiveSpace n S).CanonicallyOver S where
  hom := toBase n S

section Coefficients

variable {R R' : Type u} [CommRing R] [CommRing R']

/-- Applying a ring homomorphism coefficientwise to homogeneous polynomials defines a graded
ring homomorphism between the standard homogeneous coordinate rings. -/
def coefficientGradedRingHom (φ : R →+* R') (n : ℕ) :
    grading R n →+*ᵍ grading R' n where
  toRingHom := MvPolynomial.map φ
  map_mem hx := hx.map φ

/-- The morphism of projective spectra induced by a coefficient homomorphism, defined on its
natural open domain. -/
noncomputable def coefficientProjMap (φ : R →+* R') (n : ℕ) :
    (projMapDomain (coefficientGradedRingHom φ n)).toScheme ⟶ scheme R n :=
  projMapMap (coefficientGradedRingHom φ n)

/-- The natural domain of the projective-spectrum morphism induced by a coefficient
homomorphism is all of the target projective space. -/
theorem coefficientProjMapDomain_eq_top (φ : R →+* R') (n : ℕ) :
    projMapDomain (coefficientGradedRingHom φ n) = ⊤ := sorry

end Coefficients

end ProjectiveSpace
end AlgebraicGeometry
