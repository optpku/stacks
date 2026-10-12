/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Comma.Pseudo
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Map.Construction

/-!
# Object and `1`-cell action of relative inertia

This leaf owns the map induced by an invertibly commuting pseudo-comma square.
The `2`-cell and local-hom action live in sibling leaves.
-/

@[expose] public section

universe u v u₁ v₁

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans
open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace RelativeInertia
namespace pseudoComma

variable
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}

noncomputable section

/-- The map on relative inertia induced by an invertibly commuting square represented by a
`1`-morphism of the pseudo-comma bicategory. -/
@[stacks 04Z4 "pseudo-comma relative-inertia map"]
def map (f : S ⟶ T) :
    relativeInertia S.hom ⥤ᵇ relativeInertia T.hom :=
  RelativeInertia.map
    (Bicategory.PseudoComma.left f) (Bicategory.PseudoComma.right f)
    (Bicategory.PseudoComma.cellIso f).symm

end

end pseudoComma
end RelativeInertia
end BasedCategory
end CategoryTheory
