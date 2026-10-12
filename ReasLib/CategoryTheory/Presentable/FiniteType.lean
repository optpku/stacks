/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.CategoryTheory.Presentable.Type
public import ReasLib.CategoryTheory.Limits.Colimit.Representable
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite types and representable filtered-colimit comparisons

Finite presentability is the canonical owner of the fact that a represented Hom-functor
preserves filtered colimits.  This leaf exposes the resulting comparison-map bijectivity and its
specialization to finite types.
-/

@[expose] public section

open CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory

namespace IsFinitelyPresentable

variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable {C : Type u} [Category.{v} C]

/-- The canonical Hom-colimit comparison is bijective for a finitely presentable source. -/
@[stacks 05NR "finitely-presentable form"]
theorem colimitPost_bijective (A : C) [IsFinitelyPresentable.{v} A]
    (B : J ⥤ C) [HasColimit B] :
    Function.Bijective (colimit.post B (coyoneda.obj (op A))) := sorry

end IsFinitelyPresentable

namespace Types

variable {J : Type v} [SmallCategory J] [IsFiltered J]

/-- Lemma 19.2.3 (05NR): for a finite type `A`, the canonical map
`colim_j (A → B.obj j) → (A → colim_j B.obj j)` is bijective. -/
@[stacks 05NR]
theorem colimitPost_bijective_of_finite (A : Type (max w v)) [Finite A]
    (B : J ⥤ Type (max w v)) :
    Function.Bijective (colimit.post B (coyoneda.obj (op A))) := sorry

end Types

end CategoryTheory
