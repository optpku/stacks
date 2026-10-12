/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.InverseSystem.Preorder

/-!
# Countable inverse limits of Mittag-Leffler systems

This leaf records the countable directed-index theorem in mathlib's vocabulary for `Type`-valued
Mittag-Leffler diagrams.  It is the indexing-general prerequisite for
the sequential, image-stabilization API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.ShortComplex.ShortExact

variable {I : Type u} [Preorder I] [IsDirectedOrder I] [Countable I]

/-- A short exact row of abelian-group inverse systems remains short exact after taking its
inverse limit when its left underlying `Type`-valued diagram is Mittag-Leffler. -/
@[stacks 0598]
theorem limit_of_countable_isMittagLeffler
    {S : ShortComplex (PreorderInverseSystem I AddCommGrpCat.{v})} (hS : S.ShortExact)
    (hX₁ : (S.X₁ ⋙ forget AddCommGrpCat.{v}).IsMittagLeffler) :
    (S.map (lim : (PreorderInverseSystem I AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v})).ShortExact := sorry

end CategoryTheory.ShortComplex.ShortExact

namespace ModuleCat.ShortExact

variable {R : Type v} [Ring R]
variable {I : Type u} [Preorder I] [IsDirectedOrder I] [Countable I]

/-- Lemma 10.87.1, tag `03CA`: a short exact sequence of module-valued inverse
systems remains short exact after taking its inverse limit when the left
underlying type-valued system is Mittag-Leffler. -/
@[stacks 03CA]
theorem limit_of_countable_isMittagLeffler
    {S : ShortComplex (PreorderInverseSystem I (ModuleCat.{v} R))} (hS : S.ShortExact)
    (hX₁ : (S.X₁ ⋙ forget (ModuleCat.{v} R)).IsMittagLeffler) :
    (S.map (lim : PreorderInverseSystem I (ModuleCat.{v} R) ⥤ ModuleCat.{v} R)).ShortExact := sorry

end ModuleCat.ShortExact
