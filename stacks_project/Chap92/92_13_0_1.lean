/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Extension.Presentation.LichtenbaumSchlessinger
import StacksCheckRecall

/-!
# Lichtenbaum–Schlessinger complex of a polynomial presentation
-/

open Algebra.Presentation.LichtenbaumSchlessinger
open scoped TensorProduct

universe u

/- 92.13.0.1: for a polynomial presentation `P : Algebra.Presentation R S ι σ`,
the complex `Rel/TrivRel ⟶ F ⊗[P.Ring] S ⟶ Ω[P.Ring⁄R] ⊗[P.Ring] S`
has terms in degrees −2, −1, and 0. Its first arrow sends a relation class to its
scalar-extended relation, and its second arrow differentiates the defining polynomials.
The tensor-unit bijection below identifies the degree −2 tensor model with `Rel/TrivRel`;
the other tensor factors are reversed by the canonical `TensorProduct.comm`. -/
@[stacks 09CD] #check (Algebra.Presentation.LichtenbaumSchlessinger.complex :
  ∀ {R S ι σ : Type u} [CommRing R] [CommRing S] [Algebra R S],
    Algebra.Presentation R S ι σ → CochainComplex (ModuleCat.{u} S) ℤ)

#check (Algebra.Presentation.LichtenbaumSchlessinger.relModTrivial_baseChange_bijective :
  ∀ {R S ι σ : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Presentation R S ι σ),
    Function.Bijective (TensorProduct.mk P.Ring S (relModTrivial P) 1))

#check (Algebra.Presentation.LichtenbaumSchlessinger.toFree_mk :
  ∀ {R S ι σ : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Presentation R S ι σ) (relation : rel P),
    toFree P (Submodule.Quotient.mk relation) = 1 ⊗ₜ[P.Ring] (relation : free P))

#check (Algebra.Presentation.LichtenbaumSchlessinger.toFreeTensor_tmul_mk :
  ∀ {R S ι σ : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Presentation R S ι σ) (scalar : S) (relation : rel P),
    toFreeTensor P (scalar ⊗ₜ[P.Ring] Submodule.Quotient.mk relation) =
      scalar ⊗ₜ[P.Ring] (relation : free P))

#check (Algebra.Presentation.LichtenbaumSchlessinger.toCotangentSpace_tmul_single :
  ∀ {R S ι σ : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Presentation R S ι σ) (scalar : S) (index : σ),
    toCotangentSpace P (scalar ⊗ₜ[P.Ring] Finsupp.single index (1 : P.Ring)) =
      scalar ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring (P.relation index))
