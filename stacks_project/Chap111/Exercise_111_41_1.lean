module

public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong.LineCohomology
import StacksCheckRecall

/-!
# Exercise 111.41.1

Čech cohomology of the structure sheaf on the affine line with doubled origin, and extensions
realizing every coverwise class as the connecting value of the unit section.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.DoubledOrigin CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry LaurentPolynomial

universe u

/- Exercise 111.41.1 (1): Both overlap coordinates are sent to the same Laurent coordinate.
The negative powers give a basis of the degree-one Čech cohomology of the two-chart cover. -/
@[stacks 02F4] #check (AlgebraicGeometry.DoubledOrigin.cechH1_basis :
  ∀ (k : Type u) [Field k],
    ∃ (e : Γ(scheme k 1, chartOverlap k) ≃+* LaurentPolynomial k)
      (φ : cechH1Carrier k ≃ₗ[k] LaurentPolynomial.quotientByPolynomials k),
      (∀ p : Polynomial k,
          e (leftRestriction k (chartCoordinateRingHom k 0 p)) = Polynomial.toLaurent p) ∧
      (∀ p : Polynomial k,
          e (rightRestriction k (chartCoordinateRingHom k 1 p)) = Polynomial.toLaurent p) ∧
      (∀ n : {n : ℕ // 0 < n},
          φ (cechClassOfOverlapSection k
            (e.symm (LaurentPolynomial.T (-(n : ℤ))))) =
            LaurentPolynomial.quotientByPolynomialsMk k
              (LaurentPolynomial.T (-(n : ℤ)))) ∧
      Function.Bijective
        (Finsupp.linearCombination k
          (fun n : {n : ℕ // 0 < n} ↦
            cechClassOfOverlapSection k
              (e.symm (LaurentPolynomial.T (-(n : ℤ)))))))

/- Exercise 111.41.1 (2): Every coverwise class is the boundary of the unit section for a short
exact extension of the structure module by itself. -/
@[stacks 02F4] #check (AlgebraicGeometry.DoubledOrigin.exists_extension_of_cechClass :
  ∀ (k : Type u) [Field k] (c : cechH1 k),
    ∃ (E : (scheme k 1).toRingedSpace.Modules) (ι : unitModule k ⟶ E)
      (π : E ⟶ unitModule k) (w : ι ≫ π = 0),
      (ShortComplex.mk ι π w).ShortExact ∧ IsCoverwiseConnectingClass k ι π w c)
