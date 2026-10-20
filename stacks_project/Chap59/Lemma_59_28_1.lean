module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Kummer
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.AssociatedModule

noncomputable section

universe u

/- Lemma 59.28.1: if `n` is a unit on `S`, the Kummer sequence is short exact
on both the small and big étale sites. -/

/- Lemma 59.28.1 (1): If `n ∈ 𝒪_S^*`, the additive presentation of the Kummer
sequence is short exact on the small étale site of `S`. -/
@[stacks 03PL] #check
  (AlgebraicGeometry.Scheme.kummerSmallEtaleShortExact :
    ∀ (S : Scheme.{u}) (n : ℕ), IsUnit (n : Γ(S, ⊤)) →
      (CategoryTheory.Sheaf.kummerAddShortComplex
        (smallCommStructureSheaf .etale S) n).ShortExact)

/- Lemma 59.28.1 (2): If `n ∈ 𝒪_S^*`, the additive presentation of the Kummer
sequence is short exact on the big étale site of `S`. -/
@[stacks 03PL] #check
  (AlgebraicGeometry.Scheme.kummerBigEtaleShortExact :
    ∀ (S : Scheme.{u}) (n : ℕ), IsUnit (n : Γ(S, ⊤)) →
      (CategoryTheory.Sheaf.kummerAddShortComplex
        (bigCommStructureSheaf .etale S) n).ShortExact)

end
