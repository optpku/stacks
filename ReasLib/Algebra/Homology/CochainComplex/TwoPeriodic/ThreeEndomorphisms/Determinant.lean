/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Determinant
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ThreeEndomorphisms

/-!
# Determinants of complexes from three module endomorphisms

Under complementary image-kernel identities, the ambient, range-restricted, and
kernel-quotient complexes are exact, and their periodic determinants satisfy a product formula.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The complex on `M` with differentials `alpha` and `beta.comp gamma` is acyclic under
the complementary image-kernel identities. -/
theorem ofComposite_acyclic [IsLocalRing R] (hM : IsFiniteLength R M)
    (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.ker = (delta₁.comp delta₂).range) :
    (ofComposite alpha beta gamma hI hK).toCochainComplex.Acyclic := sorry

/-- The complex on `range gamma` with the restrictions of `alpha` and `beta` is acyclic
under the complementary image-kernel identities. -/
theorem onRange_acyclic [IsLocalRing R] (hM : IsFiniteLength R M)
    (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.ker = (delta₁.comp delta₂).range) :
    (onRange alpha beta gamma hI hK).toCochainComplex.Acyclic := sorry

/-- The complex on `M ⧸ ker beta` with the endomorphisms induced by `alpha` and `gamma`
is acyclic under the complementary image-kernel identities. -/
theorem onKerQuotient_acyclic [IsLocalRing R] (hM : IsFiniteLength R M)
    (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.ker = (delta₁.comp delta₂).range) :
    (onKerQuotient alpha beta gamma hI hK).toCochainComplex.Acyclic := sorry

/-- The periodic determinant on `M` factors as the determinant on `range gamma` followed
by the determinant on `M ⧸ ker beta`. -/
theorem determinant_ofComposite_eq_mul [IsLocalRing R] (hM : IsFiniteLength R M)
    (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.ker = (delta₁.comp delta₂).range) :
    determinant (ofComposite alpha beta gamma hI hK) hM
        (ofComposite_acyclic hM alpha beta gamma hI hK) =
      determinant (onRange alpha beta gamma hI hK)
          (hM.of_injective gamma.range.subtype_injective)
          (onRange_acyclic hM alpha beta gamma hI hK) *
        determinant (onKerQuotient alpha beta gamma hI hK)
          (hM.of_surjective (Submodule.mkQ_surjective beta.ker))
          (onKerQuotient_acyclic hM alpha beta gamma hI hK) := sorry

end CategoryTheory.TwoPeriodicEndomorphism
