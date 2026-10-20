module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Point-like decent algebraic spaces

A decent algebraic space admitting a surjective étale morphism from the spectrum of a
field is isomorphic to the spectrum of a finite separable subextension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A decent algebraic space over `S` admitting a surjective étale morphism from
`Spec(k)` is isomorphic over `S` to `Spec(k')` for a finite separable extension
`k / k'`. The given morphism agrees with the algebra-induced spectrum map under
this isomorphism, and the structure morphism of `Spec(k)` factors through `Spec(k')`. -/
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
