/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.Representable.Diagonal
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G)

/- Lemma 65.3.6: if `S` is a scheme and `a : F ⟶ G` is a representable transformation of
functors `(Over S)ᵒᵖ ⥤ Type u` on `(Sch/S)_fppf`, then the relative diagonal
`Δ_{F/G} : F ⟶ F ×_G F` is representable. -/
@[stacks 05L9]
#check (CategoryTheory.Functor.relativelyRepresentable.pullback_diagonal a :
  yoneda.relativelyRepresentable a → yoneda.relativelyRepresentable (Limits.pullback.diagonal a))
