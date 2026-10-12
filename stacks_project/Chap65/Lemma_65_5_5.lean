/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.Scheme.RepresentableProperty.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

variable {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
variable [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
variable {F G H : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : H ⟶ G)
variable [HasPullback b a]
  (ha : AlgebraicGeometry.Scheme.representableMorphismProperty S P a)

/- Lemma 65.5.5: let `S` be a scheme and let `F`, `G`, `H` be presheaves of sets
`(Over S)ᵒᵖ ⥤ Type u`. Let `P` be a property of scheme morphisms in the sense of
Definition 65.5.1. If `a : F ⟶ G` is a representable transformation with property
`P` and `b : H ⟶ G` is any transformation, then in the fibre product square of
`b` and `a` the base change `a' = pullback.fst b a` also has property `P`. -/
@[stacks 02WL]
#check (AlgebraicGeometry.Scheme.representableMorphismProperty.pullback_fst
    (P := P) a b ha :
    AlgebraicGeometry.Scheme.representableMorphismProperty S P (pullback.fst b a))
