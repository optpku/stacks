module

public import ReasLib.RingTheory.Extension.Presentation.Jacobian
public import ReasLib.RingTheory.Extension.Presentation.RelationIdeal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Selected standard data in a presentation

This leaf owns the embedding-indexed form of elementary and strict standard
data. It is independent of finite initial-coordinate presentations.

@stack 07C6
@stack 07C7
@stack 07EZ
-/

@[expose] public section

universe u v w t

namespace Algebra.Presentation

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable {ι : Type w} {σ : Type t} {c : ℕ}

/-- In a fixed presentation, `a` is elementary for selected variable and
relation embeddings when it is a multiple of their Jacobian minor and obeys
the associated relation condition. -/
@[stacks 07C6 "elementary standard data in a fixed presentation"]
def IsElementaryFor
    (P : Presentation R A ι σ) (a : A)
    (cols : Fin c ↪ ι) (rows : Fin c ↪ σ) : Prop :=
  ∃ a' : A,
    a = a' * algebraMap P.Ring A (P.jacobianMinor cols rows) ∧
      P.relationCondition a (Set.range rows)

/-- In a fixed presentation, `a` is strict for selected relation rows when it
belongs to their Jacobian ideal and obeys the associated relation condition. -/
@[stacks 07C6 "strict standard data in a fixed presentation",
  stacks 07C7 "strict standard data in a fixed presentation"]
def IsStrictlyFor
    (P : Presentation R A ι σ) (a : A) (rows : Fin c ↪ σ) : Prop :=
  a ∈ P.jacobianIdeal rows ∧ P.relationCondition a (Set.range rows)

/-- Elementary data for a fixed minor gives strict data for the same selected
relation rows. -/
@[stacks 07EZ "selected elementary data gives selected strict data"]
theorem IsElementaryFor.isStrictlyFor
    {P : Presentation R A ι σ} {a : A}
    {cols : Fin c ↪ ι} {rows : Fin c ↪ σ}
    (h : P.IsElementaryFor a cols rows) : P.IsStrictlyFor a rows := sorry

end Algebra.Presentation
