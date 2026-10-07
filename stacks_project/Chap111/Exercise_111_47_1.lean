module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hypersurface.Moduli
import StacksCheckRecall

/-!
# Exercise 111.47.1

The number of moduli of degree-`d` hypersurfaces in `P^n` over an algebraically closed
field, in the seven source specializations. Projective-linear changes are represented by
invertible `(n + 1)`-by-`(n + 1)` matrices acting on homogeneous coordinates.
-/

@[expose] public section

universe u

/- Exercise 111.47.1 (1): the number of moduli of degree-`d` hypersurfaces in `P^1` is
`d - 3`. -/
@[stacks 0EGP] #check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.Moduli.hasNumberOfModuli_P1 :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] {d : ℕ},
      1 ≤ d →
        AlgebraicGeometry.ProjectiveSpace.Hypersurface.Moduli.HasNumberOfModuli
          k 1 d (d - 3))

/- Exercise 111.47.1 (2): the number of moduli of lines in `P^2` is `0`. -/
@[stacks 0EGP] #check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.Moduli.hasNumberOfModuli_planeLine :
    ∀ {k : Type u} [Field k] [IsAlgClosed k],
      AlgebraicGeometry.ProjectiveSpace.Hypersurface.Moduli.HasNumberOfModuli k 2 1 0)

/- Exercise 111.47.1 (3): the number of moduli of plane conics is `0`. -/
@[stacks 0EGP] #check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.Moduli.hasNumberOfModuli_planeConic :
    ∀ {k : Type u} [Field k] [IsAlgClosed k],
      AlgebraicGeometry.ProjectiveSpace.Hypersurface.Moduli.HasNumberOfModuli k 2 2 0)

/- Exercise 111.47.1 (4): the number of moduli of quadrics in `P^n` is `0`. -/
@[stacks 0EGP] #check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.Moduli.hasNumberOfModuli_quadric :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ},
      1 ≤ n →
        AlgebraicGeometry.ProjectiveSpace.Hypersurface.Moduli.HasNumberOfModuli k n 2 0)

/- Exercise 111.47.1 (5): the number of moduli of plane cubics is `1`. -/
@[stacks 0EGP] #check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.Moduli.hasNumberOfModuli_planeCubic :
    ∀ {k : Type u} [Field k] [IsAlgClosed k],
      AlgebraicGeometry.ProjectiveSpace.Hypersurface.Moduli.HasNumberOfModuli k 2 3 1)

/- Exercise 111.47.1 (6): the number of moduli of cubics in `P^3` is `4`. -/
@[stacks 0EGP] #check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.Moduli.hasNumberOfModuli_cubicSurface :
    ∀ {k : Type u} [Field k] [IsAlgClosed k],
      AlgebraicGeometry.ProjectiveSpace.Hypersurface.Moduli.HasNumberOfModuli k 3 3 4)

/- Exercise 111.47.1 (7): the number of moduli of plane quartics is `6`. -/
@[stacks 0EGP] #check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.Moduli.hasNumberOfModuli_planeQuartic :
    ∀ {k : Type u} [Field k] [IsAlgClosed k],
      AlgebraicGeometry.ProjectiveSpace.Hypersurface.Moduli.HasNumberOfModuli k 2 4 6)
