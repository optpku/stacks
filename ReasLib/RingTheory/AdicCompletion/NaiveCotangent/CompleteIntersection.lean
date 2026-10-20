module

public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.JacobiZariski
public import ReasLib.Algebra.Category.CommAlgCat.AdicQuotient
public import ReasLib.RingTheory.CompleteIntersection.Local.RingHom

/-!
# Injectivity in completed cotangent homology

Stagewise local complete intersection homomorphisms induce injective
Jacobi–Zariski maps on degree-one completed naive cotangent homology.
-/

@[expose] public section

universe u

namespace Algebra.NaiveCotangent.Adic

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [IsNoetherianRing A]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
variable (I : Ideal A) [Algebra.TopologicallyFiniteType I B]
  [Algebra.TopologicallyFiniteType I C]
variable {ι κ : Type u} [Fintype ι] [Fintype κ]
variable (P : Presentation A B I ι)
variable (Q : Presentation B C (I.map (algebraMap A B)) κ)

/-- For a tower of adically complete, topologically finite type algebras over a
Noetherian ring, if every positive adic quotient map is a local complete
intersection homomorphism, then the canonical map
`H^{-1}(NL_{B/A}^∧ ⊗[B] C) ⟶ H^{-1}(NL_{C/A}^∧)` is injective. -/
@[stacks 0AQJ]
theorem homologyOneTensor_injective
    (h_lci : ∀ n : ℕ+,
      (CommAlgCat.adicQuotientMap I (IsScalarTower.toAlgHom A B C) n).IsLocalCompleteIntersection) :
    Function.Injective (homologyOneTensor I P Q) := sorry

end Algebra.NaiveCotangent.Adic
