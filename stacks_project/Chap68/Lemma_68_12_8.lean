/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Point-like decent algebraic spaces

A decent algebraic space admitting a surjective étale morphism from the spectrum of a
field is isomorphic to the spectrum of a finite separable subextension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.12.8: Let `S` be a scheme, `k` a field, and `X` a decent algebraic space
over `S`. If there is a surjective étale morphism `Spec(k) ⟶ X`, then `X` is isomorphic
over `S` to `Spec(k')` for a finite separable extension `k / k'`. -/
@[stacks 03IK]
theorem exists_iso_spec_of_surjective_etale {S : Scheme.{u}} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S} {X : AlgebraicSpace S} (f : ofOver (Over.mk σ) ⟶ X)
    [Etale f] (hf : Function.Surjective (Points.map f)) [IsDecent X] :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k' k) (σ' : Spec (.of k') ⟶ S)
      (e : X ≅ ofOver (Over.mk σ'))
      (hσ : Spec.map (CommRingCat.ofHom (algebraMap k' k)) ≫ σ' = σ),
      FiniteDimensional k' k ∧ Algebra.IsSeparable k' k ∧
        f ≫ e.hom =
          ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap k' k))) hσ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
