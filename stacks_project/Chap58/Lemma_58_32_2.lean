module

public import ReasLib.AlgebraicGeometry.AffineSpace.FiniteEtale
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 58.32.2: an étale morphism from an affine scheme to affine `n`-space over a
positive-characteristic field can be replaced by a finite étale morphism inducing the same
structure morphism to `Spec k`. -/
@[stacks 0G1G] #check (AlgebraicGeometry.AffineSpace.existsFiniteEtaleHom :
  ∀ {k : Type u} [Field k] (p n : ℕ) [CharP k p] (h_positiveChar : 0 < p)
    {X : Scheme.{u}}
    (f : X ⟶ 𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of.{u} k))) [IsAffine X] [Etale f],
    ∃ g : X ⟶ 𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of.{u} k)),
      (IsFinite g ∧ Etale g) ∧
        g ≫ (𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of.{u} k)) ↘ Spec (CommRingCat.of.{u} k)) =
          f ≫ (𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of.{u} k)) ↘ Spec (CommRingCat.of.{u} k)))
