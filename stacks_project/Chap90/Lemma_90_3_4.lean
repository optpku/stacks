/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.Length
public import ReasLib.RingTheory.LocalRing.Length.ResidueImage

/-!
# Length of a module over a local `Λ`-algebra

For a local `Λ`-algebra with residue field `k`, length over `Λ` differs from length
over `A` by the finite degree of `k` over `residueImage Λ k`. In the classical case the
degree is `1`.
-/

@[expose] public section

open Algebra
open IsLocalRing

universe u v w

/- Lemma 90.3.4 (1): if `A` is a local `Λ`-algebra with residue field identified with `k`,
then restriction of scalars multiplies module length by `[k : residueImage Λ k]`. -/
@[stacks 06GG] #check
  (IsLocalRing.length_mul_finrank_eq_length :
    ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ]
      [Field k] [Algebra Λ k] [Module.Finite Λ k]
      {A : Type v} [CommRing A] [IsLocalRing A] [Algebra Λ A]
      (_ : ResidueField A ≃ₐ[Λ] k) {M : Type w}
      [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower Λ A M],
      (Module.finrank (residueImage Λ k) k : ℕ∞) * Module.length A M =
        Module.length Λ M)

/- Lemma 90.3.4 (2): in the classical case, module length over `A` equals module length
over `Λ`. -/
@[stacks 06GG] #check
  (IsLocalRing.length_eq_of_classical :
    ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ]
      [Field k] [Algebra Λ k] [Module.Finite Λ k]
      [ArtinianLocalAlgCat.IsClassical Λ k]
      {A : Type v} [CommRing A] [IsLocalRing A] [Algebra Λ A]
      (_ : ResidueField A ≃ₐ[Λ] k) {M : Type w}
      [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower Λ A M],
      Module.length A M = Module.length Λ M)
