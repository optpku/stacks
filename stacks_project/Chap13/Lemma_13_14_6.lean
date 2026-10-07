module

import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Triangulated
import StacksCheckRecall

@[expose] public section

/-!
# Derived Functors and Distinguished Triangles

The reusable statement and its pointwise-value triangle live in the model-independent
`ReasLib.CategoryTheory.Functor.Derived` hierarchy.  This chapter file records the source-facing
clauses without retaining a second implementation of denominator-triangle infrastructure.
-/

open CategoryTheory

/-
Lemma 13.14.6 (05SC): for an exact functor of triangulated categories and a saturated
multiplicative system compatible with triangulation, source-definedness of `RF` at any two
vertices of a distinguished triangle implies source-definedness at the third, and the canonical
triangle of derived values is distinguished.  The same statements hold for `LF`.
-/

@[stacks 05SC "(1)"] #check @Functor.RightDerived.DefinedAt.Triangle.obj₃
@[stacks 05SC "(2)"] #check @Functor.RightDerived.DefinedAt.Triangle.obj₁
@[stacks 05SC "(3)"] #check @Functor.RightDerived.DefinedAt.Triangle.obj₂
@[stacks 05SC "(4)"] #check @Functor.LeftDerived.DefinedAt.Triangle.obj₃
@[stacks 05SC "(5)"] #check @Functor.LeftDerived.DefinedAt.Triangle.obj₁
@[stacks 05SC "(6)"] #check @Functor.LeftDerived.DefinedAt.Triangle.obj₂
@[stacks 05SC "(7)"] #check @Functor.RightDerived.DefinedAt.Triangle.valueDistinguished
@[stacks 05SC "(8)"] #check @Functor.LeftDerived.DefinedAt.Triangle.valueDistinguished

#check @Functor.RightDerived.DefinedAt.triangulated
#check @Functor.LeftDerived.DefinedAt.triangulated
#check @Functor.RightDerived.Value.triangle
#check @Functor.LeftDerived.Value.triangle
