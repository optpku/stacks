module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.CategoryTheory.MorphismProperty.Representable.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

variable {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u}
variable (a : F ⟶ G) (b : H ⟶ G) [HasPullback b a]
variable (ha : yoneda.relativelyRepresentable a)

/- Lemma 65.3.3: let `S` be a scheme and let `F`, `G`, `H` be functors
`(Over S)ᵒᵖ ⥤ Type u`. If `a : F ⟶ G` is a representable transformation of functors and
`b : H ⟶ G` is any transformation, then the base change `a' = pullback.fst b a` in the
fibre product square of `b` and `a` is a representable transformation of functors. -/
@[stacks 02WB]
#check (CategoryTheory.Functor.relativelyRepresentable.pullback_fst b a ha :
  yoneda.relativelyRepresentable (pullback.fst b a))
