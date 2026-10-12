/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Homotopy
import StacksCheckRecall

/-!
@stack 019M

# Source-facing recall for Remark 14.26.4

The mathlib homotopy construction works over an arbitrary category and is functorial in the
ambient category. ReasLib lifts that functoriality to the zigzag homotopy relation.
-/

@[expose] public section

namespace CategoryTheory.SimplicialObject

universe u v u' v'

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]
variable {U V : SimplicialObject C} {a b : U ⟶ V}
variable (h : Homotopic a b) (H : Homotopy a b) (F : C ⥤ D)

/- Remark 14.26.4: functors preserve the zigzag simplicial homotopy relation. -/
@[stacks 019M]
#check (h.whiskerRight F :
  Homotopic (Functor.whiskerRight a F) (Functor.whiskerRight b F))

/- The directed homotopy construction underlying the zigzag statement is also functorial. -/
#check (H.whiskerRight F :
  Homotopy (((whiskering C D).obj F).map a) (((whiskering C D).obj F).map b))

end CategoryTheory.SimplicialObject
