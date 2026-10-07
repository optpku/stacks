module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import StacksCheckRecall

@[expose] public section

universe w v u

namespace CategoryTheory

section Complex

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {n : ℕ} (S : ComposableArrows C n)

/- Definition 12.5.7 (1): a finite sequence is a complex when every composite of two
consecutive arrows vanishes. -/
@[stacks 010E] #check (S.IsComplex : Prop)

variable {ι : Type w} (c : ComplexShape ι)

/- Definition 12.5.7 (2): arbitrary one-sided and two-sided complexes are modeled by a
`ComplexShape` rather than by separate source-specific sequence types. -/
#check (HomologicalComplex C c : Type (max (max u w) v))
#check (ChainComplex C ℤ : Type (max u v))
#check (CochainComplex C ℤ : Type (max u v))

end Complex

section Exact

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {n : ℕ} (S : ComposableArrows C n)

/- Definition 12.5.7 (3): a finite sequence is exact when it is a complex and is exact at
every internal object. -/
#check (S.Exact : Prop)

variable {ι : Type w} {c : ComplexShape ι} (K : HomologicalComplex C c) (i : ι)

/- Definition 12.5.7 (4): exactness at one degree and exactness at every degree use the
canonical `ExactAt` and `Acyclic` predicates. -/
#check (K.ExactAt i : Prop)
#check (K.Acyclic : Prop)

variable (T : ShortComplex C)

/- Definition 12.5.7 (5): three-term exactness is owned by `ShortComplex.Exact`. -/
#check (T.Exact : Prop)

/- Definition 12.5.7 (6): a short exact sequence is an exact short complex whose first map
is mono and whose second map is epi. -/
#check (T.ShortExact : Prop)

end Exact

end CategoryTheory
