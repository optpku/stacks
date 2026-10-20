module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Presheaf
import StacksCheckRecall

/-!
# Maps of presheaves representable by algebraic spaces

A map of set-valued presheaves on `(Sch/S)_fppf` is representable by algebraic
spaces if and only if the associated map of categories fibred in sets is.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 94.9.5: let `S` be an object of `Sch_fppf`. Let `a : F ⟶ G` be a map of
presheaves of sets on `(Sch/S)_fppf`. Denote `a' : 𝒮_F ⟶ 𝒮_G` the associated
map of categories fibred in sets. Then `a` is representable by algebraic spaces
in the sense of Bootstrap Definition 80.3.1 if and only if `a'` is representable
by algebraic spaces. -/
@[stacks 0458] #check
  (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.iff_ofPresheaf :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G),
    AlgebraicSpace.representableByAlgebraicSpaces a ↔
      relativelyRepresentableByAlgebraicSpaces
        ((Sets.toGroupoids (Over S)).map ((Sets.ofPresheaf (Over S)).map a)))

end AlgebraicGeometry
