/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Naturality.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.Action.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative-to-absolute inertia comparison on pseudo-comma arrows

This leaf owns the canonical comparison for a pseudo-comma square.  Its computational
readouts and compatibility with pseudo-comma `2`-cells are layered separately.
-/

@[expose] public section

universe u v u₁ v₁

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans

variable {C : Type u} [Category.{v} C]

namespace RelativeInertia
namespace pseudoComma

variable
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}

noncomputable section

/-- Mapping relative inertia along a pseudo-comma square and then forgetting
the relative condition is canonically isomorphic to first forgetting that
condition and mapping absolute inertia along the left endpoint. -/
@[stacks 04Z5 "pseudo-comma relative-to-absolute inertia comparison"]
def toInertiaIso (f : S ⟶ T) :
    pseudoComma.map f ⋙ RelativeInertia.toInertia T.hom ≅
      RelativeInertia.toInertia S.hom ⋙ Inertia.map (Bicategory.PseudoComma.left f) :=
  RelativeInertia.toInertia.naturalityIso
    (Bicategory.PseudoComma.left f) (Bicategory.PseudoComma.right f)
    (Bicategory.PseudoComma.cellIso f).symm

end

end pseudoComma
end RelativeInertia
end BasedCategory
end CategoryTheory
