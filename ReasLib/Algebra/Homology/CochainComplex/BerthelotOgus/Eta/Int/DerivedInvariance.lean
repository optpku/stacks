module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.AlternatingRank
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.RingTheory.Ideal.Principal

/-!
# Derived invariance of integer eta determinantal ideals

The eta determinantal ideal of a bounded-above finite-free representative is invariant under
derived isomorphism after the canonical power correction determined by its alternating rank.
@stack 0GSS
-/

@[expose] public section

open CategoryTheory
open scoped BerthelotOgus nonZeroDivisors

noncomputable section

universe u

namespace CochainComplex.BerthelotOgus.Int.DeterminantalIdeal

variable {A : Type u} [CommRing A]

/-- Derived-isomorphic bounded-above finite-free complexes have the same eta determinantal ideal
after balancing their alternating ranks by powers of the nonzerodivisor. -/
theorem pow_mul_eq_of_isIsomorphic
    (f : A) (hf : f ∈ nonZeroDivisors A)
    {K L : CochainComplex (ModuleCat A) ℤ} (i : ℤ)
    [K.IsTermwiseFiniteFree] [L.IsTermwiseFiniteFree]
    {bK bL : ℤ} (hK : K.IsStrictlyLE bK) (hL : L.IsStrictlyLE bL)
    (hKL : IsIsomorphic (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L))
    {m n : ℕ}
    (hbalance :
      (m : ℤ) + alternatingRank K i bK =
        (n : ℤ) + alternatingRank L i bL) :
    principalIdeal (f ^ m) * I[f]_(i)(K) =
      principalIdeal (f ^ n) * I[f]_(i)(L) := sorry

/-- Lemma 15.97.1, Tag 0GSS: derived-isomorphic bounded complexes of finite free modules have
the same eta determinantal ideal after the alternating-rank power correction.  The explicit upper
bounds select finite representatives for the two alternating tails. -/
@[stacks 0GSS "derived invariance of Berthelot-Ogus determinantal ideals"]
theorem pow_mul_eq_of_isIsomorphic_of_bounded
    (f : A) (hf : f ∈ nonZeroDivisors A)
    {K L : CochainComplex (ModuleCat A) ℤ} (i : ℤ)
    (hKbounded : CochainComplex.bounded (ModuleCat A) K)
    (hLbounded : CochainComplex.bounded (ModuleCat A) L)
    [K.IsTermwiseFiniteFree] [L.IsTermwiseFiniteFree]
    {bK bL : ℤ} (hK : K.IsStrictlyLE bK) (hL : L.IsStrictlyLE bL)
    (hKL : IsIsomorphic (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L))
    {m n : ℕ}
    (hbalance :
      (m : ℤ) + alternatingRank K i bK =
        (n : ℤ) + alternatingRank L i bL) :
    principalIdeal (f ^ m) * I[f]_(i)(K) =
      principalIdeal (f ^ n) * I[f]_(i)(L) := sorry

end CochainComplex.BerthelotOgus.Int.DeterminantalIdeal
