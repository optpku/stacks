/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_7_3_CompleteLocal
public import stacks_project.Chap90.Lemma_90_4_7_AdicTopology

/-!
# Maximal-adic topology after quotient by an intersection

In the completed base category, a decreasing family of ideals containing the
maximal-adic powers induces the maximal-adic topology on the quotient by the
intersection.
-/

@[expose] public section

open IsLocalRing CompleteLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- Lemma 90.4.7: if `R` is an object of `Ĉ_Λ = CompleteLocalAlgCat Λ k` and `J` is a
decreasing sequence of ideals with `maximalIdeal R.carrier ^ n ≤ J n`, then writing
`I` for `⨅ i, J i`, the sequence of images `(J n).map (Ideal.Quotient.mk I)` defines
the `maximalIdeal (R.carrier ⧸ I)`-adic topology on `R.carrier ⧸ I`. -/
@[stacks 06SE]
theorem definesMaximalAdicTopology_map_iInf (R : CompleteLocalAlgCat Λ k)
    (J : ℕ → Ideal R.carrier) (hJ_anti : Antitone J)
    (hJ_pow : ∀ n, maximalIdeal R.carrier ^ n ≤ J n)
    [IsLocalRing (R.carrier ⧸ ⨅ i, J i)] :
    let I := ⨅ i, J i;
    (∀ n, maximalIdeal (R.carrier ⧸ I) ^ n ≤ (J n).map (Ideal.Quotient.mk I)) ∧
      ∀ n, ∃ N, (J N).map (Ideal.Quotient.mk I) ≤
        maximalIdeal (R.carrier ⧸ I) ^ n := sorry

end CompleteLocalAlgCat
