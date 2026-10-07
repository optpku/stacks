module

public import ReasLib.AlgebraicTopology.SimplicialObject.Skeleton.NormalizedMoore
import StacksCheckRecall

/-!
@stack 018T

# Lemma 14.21.9 compatibility facade

The lower-face normalized-Moore vanishing theorem for a truncated simplicial skeleton is owned
by ReasLib.
-/

@[expose] public section

open CategoryTheory AlgebraicTopology

universe u v

namespace CategoryTheory.SimplicialObject.Truncated

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (m n : ℕ) (U : SimplicialObject.Truncated A m)

/- Lemma 14.21.9: lower-face normalized Moore objects of `i_{m!} U` vanish above degree `m`. -/
@[stacks 018T]
#check (sk.normalizedMoore.lowerFace.eq_bot_of_lt U :
  m < n → SimplicialObject.normalizedMoore.lowerFace.subobject
    ((Truncated.sk m).obj U) n = ⊥)

end CategoryTheory.SimplicialObject.Truncated
