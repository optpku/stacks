/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Kummer
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.AssociatedModule

noncomputable section

universe u

/- Remark 59.28.4 (1): Lemma 59.28.3 is false for the big smooth topology. -/
@[stacks 040O] #check
  (AlgebraicGeometry.Scheme.kummerBigSmoothNotUniversallyShortExact :
    ¬ ∀ (S : Scheme.{u}) (n : ℕ), 0 < n →
      (CategoryTheory.Sheaf.kummerAddShortComplex
        (AlgebraicGeometry.Scheme.AssociatedModule.bigCommStructureSheaf
          .smooth S) n).ShortExact)

/- Remark 59.28.4 (2): Lemma 59.28.3 is false for the big étale topology. -/
@[stacks 040O] #check
  (AlgebraicGeometry.Scheme.kummerBigEtaleNotUniversallyShortExact :
    ¬ ∀ (S : Scheme.{u}) (n : ℕ), 0 < n →
      (CategoryTheory.Sheaf.kummerAddShortComplex
        (AlgebraicGeometry.Scheme.AssociatedModule.bigCommStructureSheaf
          .etale S) n).ShortExact)

/- Remark 59.28.4 (3): Lemma 59.28.3 is false for the big Zariski topology. -/
@[stacks 040O] #check
  (AlgebraicGeometry.Scheme.kummerBigZariskiNotUniversallyShortExact :
    ¬ ∀ (S : Scheme.{u}) (n : ℕ), 0 < n →
      (CategoryTheory.Sheaf.kummerAddShortComplex
        (AlgebraicGeometry.Scheme.AssociatedModule.bigCommStructureSheaf
          .zariski S) n).ShortExact)

end
