/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Strict
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe v u

noncomputable section

/-!
# Strict Monomorphisms and Epimorphisms

For a monomorphism, strictness says that the source filtration is induced.  Dually, for an
epimorphism it says that the target filtration is the quotient filtration.
-/

namespace CategoryTheory
namespace FilteredObject.Hom

variable {C : Type u} [Category.{v} C] [HasImages C] [HasPullbacks C] [HasEqualizers C]
variable {A B : FilteredObject C} (f : A ⟶ B)

-- Proof sketch: pull back the stagewise strictness identity along the monomorphism `f.hom`.
-- Because pullback along a mono inverts the forward-map functor on subobjects, the left side
-- becomes the source filtration stage; the right side becomes the pullback of the target stage.
/-- For an injective morphism of filtered objects, strictness is equivalent to
the source filtration agreeing stagewise with the induced filtration. We keep the right-hand side
on `A.obj`, so it is written in the pullback form underlying `DecreasingFiltration.induced`. -/
@[stacks 0124]
theorem strict_iff_induced_filtration_of_mono [Mono f.hom] :
    Strict f ↔
      A.filtration = (Subobject.pullback f.hom).toOrderHom.comp B.filtration := sorry

-- Proof sketch: when `f.hom` is epi, `imageSubobject f.hom = ⊤`, so the stagewise strictness
-- equality becomes the statement that each target filtration stage is the image of the
-- corresponding source filtration stage under `f.hom`.
/-- For a surjective morphism of filtered objects, strictness is equivalent to
the target filtration agreeing stagewise with the quotient filtration. -/
@[stacks 0124]
theorem strict_iff_quotient_filtration_of_epi [Balanced C] [Epi f.hom] :
    Strict f ↔ B.filtration = A.filtration.quotient f.hom := sorry

end FilteredObject.Hom
end CategoryTheory
