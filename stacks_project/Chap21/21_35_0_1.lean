/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

universe u v

/- 21.35.0.1 (08J8): in the closed braided monoidal derived category of modules on a ringed
site, currying gives the canonical equivalence
`(K ⟶ (ihom L).obj M) ≃ (K ⊗ L ⟶ M)`.  The reusable owner is independent of the chosen
ringed-site model. -/
@[stacks 08J8]
#check fun {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A]
    [MonoidalClosed A] (K L M : A) ↦
  (braidedHomEquiv K L M).symm

#check @MonoidalClosed.braidedHomEquiv_symm_apply
