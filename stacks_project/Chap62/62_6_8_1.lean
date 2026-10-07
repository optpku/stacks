module

public import stacks_project.Chap62.«62_6_8_1_CycleClass»
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- 62.6.8.1: Let `S` be a locally Noetherian scheme. Let `f : X ⟶ S` be a morphism
which is of finite type. Let `r ≥ 0`. Denote `Hilb(X/S, r)` the set of closed
subschemes `Z ⊂ X` such that `Z ⟶ S` is flat and of relative dimension `≤ r`.
Each such `Z` determines a relative `r`-cycle `[Z/X/S]_r`, and linear extension
yields a group homomorphism from the free abelian group on `Hilb(X/S, r)` to
`z(X/S, r)`, sending `∑ n_i [Z_i]` to `∑ n_i [Z_i/X/S]_r`. -/
@[stacks 0H58]
#check fun {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) ↦
  (RelativeCycle.cycleClassHomToGroup f r :
    FreeAbelianGroup (RelativeCycle.Hilb f r) →+ RelativeCycle.group f r)
