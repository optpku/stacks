/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Injective.FrobeniusTorsion
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w

/- Lemma 51.18.2: over a regular local ring `A` of prime characteristic `p`, an
`IsLocalRing.maximalIdeal A`-power torsion module invariant under scalar extension
along Frobenius is isomorphic to a direct sum of copies of an injective hull of the
residue field. -/
@[stacks 0EC3] #check (Module.equivDirectSumInjectiveHull_of_frobeniusBaseChange :
  ∀ (p : ℕ) [Fact p.Prime] {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (hp : (p : A) = 0) (M : Type (max u v)) (E : Type w)
    [AddCommGroup M] [Module A M] [AddCommGroup E] [Module A E]
    [Module.Injective A E] (ι : IsLocalRing.ResidueField A →ₗ[A] E)
    (hι : ι.IsInjectiveHull)
    (hM : Module.IsIdealPowerTorsion (IsLocalRing.maximalIdeal A) M)
    (hF : Nonempty
      ((ModuleCat.extendScalars (RingHom.frobeniusOfPrime p hp)).obj
        (ModuleCat.of A M) ≅ ModuleCat.of A M)),
    ∃ J : Type (max u v), Nonempty (M ≃ₗ[A] DirectSum J (fun _ ↦ E)))
