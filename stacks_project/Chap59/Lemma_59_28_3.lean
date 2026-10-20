module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Kummer
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.AssociatedModule

noncomputable section

universe u

/-
Lemma 59.28.3 (1): For every scheme `S` and positive natural number `n`, the
Kummer sequence of units sheaves is short exact on the big fppf site of `S`.
Here `0 < n` records the source's positive-integer convention.
-/
@[stacks 040N] #check
  (AlgebraicGeometry.Scheme.kummerBigFppfShortExact :
    ∀ (S : Scheme.{u}) (n : ℕ) (h_pos : 0 < n),
      (CategoryTheory.Sheaf.kummerAddShortComplex
        (bigCommStructureSheaf .fppf S) n).ShortExact)

/-
Lemma 59.28.3 (2): For every scheme `S` and positive natural number `n`, the
Kummer sequence of units sheaves is short exact on the big syntomic site of
`S`. Here `0 < n` records the source's positive-integer convention.
-/
@[stacks 040N] #check
  (AlgebraicGeometry.Scheme.kummerBigSyntomicShortExact :
    ∀ (S : Scheme.{u}) (n : ℕ) (h_pos : 0 < n),
      (CategoryTheory.Sheaf.kummerAddShortComplex
        (bigCommStructureSheaf .syntomic S) n).ShortExact)

end
