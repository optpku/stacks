module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.BaseChange
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 27.13.2: projective `n`-space over a scheme is the base change of projective
`n`-space over `ℤ`. -/
@[stacks 01NF] #check (AlgebraicGeometry.ProjectiveSpace :
  ℕ → AlgebraicGeometry.Scheme.{u} → AlgebraicGeometry.Scheme.{u})

/- The standard projective `n`-space over a ring is the `Proj` of the standard homogeneous
grading on the polynomial ring in `n + 1` variables. -/
#check (AlgebraicGeometry.ProjectiveSpace.scheme :
  ∀ (R : Type u) [CommRing R], ℕ → AlgebraicGeometry.Scheme.{u})

/- The standard projective space over a ring has its canonical morphism to the ring spectrum. -/
#check (AlgebraicGeometry.ProjectiveSpace.toSpec :
  ∀ (R : Type u) [CommRing R] (n : ℕ),
    AlgebraicGeometry.ProjectiveSpace.scheme R n ⟶ AlgebraicGeometry.Spec (.of R))

/- Projective space over a scheme has its canonical projection to the base scheme. -/
#check (AlgebraicGeometry.ProjectiveSpace.toBase :
  ∀ (n : ℕ) (S : AlgebraicGeometry.Scheme.{u}),
    AlgebraicGeometry.ProjectiveSpace n S ⟶ S)

/- Projective space over a scheme carries its canonical over-base structure. -/
#check (AlgebraicGeometry.ProjectiveSpace.over :
  ∀ (n : ℕ) (S : AlgebraicGeometry.Scheme.{u}),
    AlgebraicGeometry.Scheme.CanonicallyOver
      (AlgebraicGeometry.ProjectiveSpace n S) S)

section

variable (R : Type u) [CommRing R] (n : ℕ)

/- Projective `n`-space over a ring is the base change to the spectrum of that ring. -/
#check (AlgebraicGeometry.ProjectiveSpace n (AlgebraicGeometry.Spec (.of R)) :
  AlgebraicGeometry.Scheme.{u})

end
