/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.DoldKan.DegenerateImages
import StacksCheckRecall

/-!
# Remark 14.23.7 compatibility facade

@stack 0FKI

The reusable owner is the categorical `degenerateSubobject` coproduct-map API for an arbitrary
simplex `Δ`. Its `AddCommGrpCat` generator-and-span description is a concrete companion rather
than the root owner.
-/

@[expose] public section

open AlgebraicTopology
open CategoryTheory
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.DoldKan

section Categorical

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (U : SimplicialObject A) (n : ℕ)

/- Remark 14.23.7 (1) (Stacks 0FKI): the degenerate term is the image of the coproduct of
lower-dimensional terms indexed by proper epimorphisms. -/
@[stacks 0FKI "Remark 14.23.7 (1)"]
#check (degenerateSubobject.eq_image U n :
  degenerateSubobject U n =
    degenerateSubobject.image U (Opposite.op ⦋n⦌))

#check degenerateSubobject.Index
#check degenerateSubobject.summand
#check (degenerateSubobject.source U)
#check (degenerateSubobject.desc U)
#check degenerateSubobject.desc.ι
#check degenerateSubobject.source.map
#check degenerateSubobject.source.functor
#check degenerateSubobject.desc.naturality
#check degenerateSubobject.desc.natTrans
#check (degenerateSubobject.image U)

end Categorical

section Elements

variable (V : SimplicialObject AddCommGrpCat.{u}) (n : ℕ)

/- Remark 14.23.7 (2) (Stacks 0FKI): for simplicial abelian groups, the elements are generated
by the ranges of the proper-epimorphism structure maps. -/
@[stacks 0FKI "Remark 14.23.7 (2)"]
#check (degenerateSimplex.span.coe_eq_range V n :
  (degenerateSimplex.span V n : Set (V _⦋n⦌)) =
    Set.range (degenerateSubobject V n).arrow)

#check (degenerateSimplex.generators V)
#check degenerateSimplex.generators.mem_iff
#check degenerateSimplex.generators.succ
#check (degenerateSimplex.span V)
#check degenerateSimplex.span.mem_iff

end Elements

end AlgebraicTopology.DoldKan
