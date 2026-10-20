module

public import ReasLib.RepresentationTheory.Coinvariants

/-!
# Coinvariants of monoid-algebra modules

The quotient and descent API is provided by the shared coinvariants owner.
-/

universe u v w x

open scoped MonoidAlgebra

#check (MonoidAlgebra.Coinvariants :
    ∀ (Λ : Type u) (G : Type v) (P : Type w) [Ring Λ] [Monoid G] [AddCommGroup P]
    [Module (Λ[G]) P] [Module Λ P], Type w)

#check (MonoidAlgebra.Coinvariants.lift :
    ∀ (Λ : Type u) (G : Type v) (P : Type w) [Ring Λ] [Monoid G] [AddCommGroup P]
    [Module (Λ[G]) P] [Module Λ P] {M : Type x} [AddCommGroup M] [Module Λ M]
    (f : P →ₗ[Λ] M)
    (_ : ∀ g : G, ∀ p : P, f ((MonoidAlgebra.single g (1 : Λ) : Λ[G]) • p) = f p),
    MonoidAlgebra.Coinvariants Λ G P →ₗ[Λ] M)
