module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Kummer
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.AssociatedModule

noncomputable section

universe u

/- Remark 59.28.2: The Kummer short-exactness assertion fails on the big
Zariski topology, while exactness also holds on the big smooth site. -/

/- Remark 59.28.2 (1): Replacing étale by Zariski can destroy short
exactness for the Kummer sequence. -/
@[stacks 03PM]
#check (AlgebraicGeometry.Scheme.kummerBigZariskiNotShortExact :
    ∃ (S : Scheme.{u}) (n : ℕ),
      0 < n ∧ IsUnit (n : Γ(S, ⊤)) ∧
        ¬ (CategoryTheory.Sheaf.kummerAddShortComplex
          (bigCommStructureSheaf .zariski S) n).ShortExact)

/- Remark 59.28.2 (2): The Kummer sequence is short exact on the big smooth
site. -/
@[stacks 03PM]
#check (AlgebraicGeometry.Scheme.kummerBigSmoothShortExact :
    ∀ (S : Scheme.{u}) (n : ℕ), IsUnit (n : Γ(S, ⊤)) →
      (CategoryTheory.Sheaf.kummerAddShortComplex
        (bigCommStructureSheaf .smooth S) n).ShortExact)

end
