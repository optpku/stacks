/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.«94_8_2_1_FullyFaithful»
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory
open scoped Bicategory

/- 94.8.2.1: if categories fibred in groupoids X, Y over (Sch/S)_fppf are
representable by algebraic spaces F, G, then 1-morphisms X ⟶ Y up to
2-isomorphism are identified with morphisms F ⟶ G of algebraic spaces.
HomotopyCategory morphisms are the 2-isomorphism classes, and the suppressed
equivalences X ≌ F.toGroupoids and Y ≌ G.toGroupoids are the explicit
parameters of homEquiv. -/
@[stacks 04SW]
#check AlgebraicSpace.toGroupoids.homEquiv
