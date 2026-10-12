/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Infinitesimal lifting for formally etale algebras

The canonical owner is Mathlib's `Algebra.FormallyEtale`.  This leaf exposes
its unique-lift formulation over an ambient algebra structure, so public
statements do not install a ring homomorphism's algebra structure with a
`letI`.
-/

universe u v w

namespace Algebra.FormallyEtale

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- An algebra is formally etale exactly when every map to a square-zero
quotient has a unique lift.  The test algebra lives in the canonical universe
used by Mathlib's recognition theorem. -/
@[stacks 00UQ "unique infinitesimal lifting criterion"]
theorem iff_existsUnique_lift :
    Algebra.FormallyEtale R S ↔
      ∀ ⦃A : Type (max u v)⦄ [CommRing A] [Algebra R A]
        (I : Ideal A) (hI : I ^ 2 = ⊥) (g : S →ₐ[R] A ⧸ I),
          ∃! g' : S →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp g' = g := sorry
/- Proof strategy: rewrite `Function.Bijective` in
`Algebra.FormallyEtale.iff_comp_bijective` as pointwise unique existence. -/

/-- A formally etale algebra has unique lifts through square-zero quotients
in every target universe. -/
@[stacks 00UQ "formally etale unique lift"]
theorem existsUnique_lift [Algebra.FormallyEtale R S]
    {A : Type w} [CommRing A] [Algebra R A]
    (I : Ideal A) (hI : I ^ 2 = ⊥) (g : S →ₐ[R] A ⧸ I) :
    ∃! g' : S →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp g' = g := sorry
/- Proof strategy: evaluate `Algebra.FormallyEtale.comp_bijective R S I hI`
at `g` and rewrite bijectivity as unique existence. -/

/-- Construct formal etaleness from unique infinitesimal lifting in the
canonical test universe. -/
@[stacks 00UQ "formal etaleness from unique lifts"]
theorem of_existsUnique_lift
    (h : ∀ ⦃A : Type (max u v)⦄ [CommRing A] [Algebra R A]
      (I : Ideal A) (hI : I ^ 2 = ⊥) (g : S →ₐ[R] A ⧸ I),
        ∃! g' : S →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp g' = g) :
    Algebra.FormallyEtale R S := sorry
/- Proof strategy: apply the reverse direction of `iff_existsUnique_lift`. -/

end Algebra.FormallyEtale
