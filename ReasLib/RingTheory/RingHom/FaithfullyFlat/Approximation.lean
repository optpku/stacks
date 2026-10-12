/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite-presentation models of faithfully flat maps

This leaf owns the map-level approximation statement for a faithfully flat
finitely presented commutative algebra.  Its output is expressed by the
canonical `Algebra.IsPushout` square rather than by a chosen tensor-product
equivalence, so it remains independent of a particular presentation.
-/

universe u v w

namespace RingHom.FaithfullyFlat

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra.FinitePresentation A B]

/-- A faithfully flat finitely presented map of commutative `R`-algebras has a
finitely presented faithfully flat model over a finitely presented `R`-algebra.
The comparison with the original map is the canonical pushout square
`Algebra.IsPushout A₀ A B₀ B`. -/
@[stacks 034Y "faithfully flat finite-presentation base-change model"]
theorem exists_model
    (hff : (algebraMap A B).FaithfullyFlat) :
    ∃ (A₀ : Type (max u v w)) (_ : CommRing A₀) (r : R →+* A₀) (a : A₀ →+* A),
      ∃ (ha : a.comp r = algebraMap R A),
      r.FinitePresentation ∧
      ∃ (B₀ : Type (max u v w)) (_ : CommRing B₀) (g : A₀ →+* B₀) (b : B₀ →+* B),
        ∃ (hb : b.comp g = (algebraMap A B).comp a),
        g.FinitePresentation ∧
        g.FaithfullyFlat ∧
        let _ : Algebra A₀ A := a.toAlgebra
        let _ : Algebra A₀ B₀ := g.toAlgebra
        let _ : Algebra B₀ B := b.toAlgebra
        let _ : Algebra A₀ B := ((algebraMap A B).comp a).toAlgebra
        let _ : IsScalarTower A₀ A B := IsScalarTower.of_algebraMap_eq' rfl
        let _ : IsScalarTower A₀ B₀ B := IsScalarTower.of_algebraMap_eq' hb.symm
        Algebra.IsPushout A₀ A B₀ B := sorry

end RingHom.FaithfullyFlat
