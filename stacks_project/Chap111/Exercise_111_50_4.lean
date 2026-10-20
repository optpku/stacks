module

public import ReasLib.RingTheory.Smooth.Hypersurface
import StacksCheckRecall

@[expose] public section

universe u v w

/- Exercise 111.50.4: if `A = R[x, y] ⧸ (f)` and the images of its two partial
derivatives generate the unit ideal, every `R`-algebra map from `A` lifts along
a surjective `R`-algebra map whose kernel has square zero. -/
@[stacks 02FF] #check (Algebra.FormallySmooth.exists_lift_of_hypersurfaceJacobianIdeal :
  ∀ {R : Type u} {B' : Type v} {B : Type w} [CommRing R] [CommRing B'] [CommRing B]
    [Algebra R B'] [Algebra R B] (f : MvPolynomial (Fin 2) R)
    (hjac : Algebra.hypersurfaceJacobianIdeal f = ⊤) (π : B' →ₐ[R] B)
    (hπ : Function.Surjective π) (hker : (RingHom.ker π) ^ 2 = ⊥)
    (φ : (MvPolynomial (Fin 2) R ⧸ Ideal.span {f}) →ₐ[R] B),
    ∃ φ' : (MvPolynomial (Fin 2) R ⧸ Ideal.span {f}) →ₐ[R] B',
      π.comp φ' = φ)
