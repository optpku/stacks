/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation.Pullback
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

/- Lemma 70.3.6: Let `S` be a scheme contained in `Sch_fppf`. Let `E`, `F`,
`G`, `H : (Over S)ᵒᵖ ⥤ Type v`. Let `a : F ⟶ G`, `b : H ⟶ G`, and
`c : G ⟶ E` be transformations of functors. If `c`, `a ≫ c`, and `b ≫ c`
are limit preserving, then `F ×_G H ⟶ E` is limit preserving. -/
@[stacks 0GDZ] #check
  (AlgebraicGeometry.Scheme.Over.IsLimitPreserving.pullback_comp :
    ∀ {S : Scheme.{u}} {E F G H P : (Over S)ᵒᵖ ⥤ Type v}
      {a : F ⟶ G} {b : H ⟶ G} {c : G ⟶ E} {a' : P ⟶ H} {b' : P ⟶ F},
      CategoryTheory.IsPullback b' a' a b →
      AlgebraicGeometry.Scheme.Over.IsLimitPreserving c →
      AlgebraicGeometry.Scheme.Over.IsLimitPreserving (a ≫ c) →
      AlgebraicGeometry.Scheme.Over.IsLimitPreserving (b ≫ c) →
      AlgebraicGeometry.Scheme.Over.IsLimitPreserving (b' ≫ a ≫ c))
