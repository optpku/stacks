module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Equivalence
import StacksCheckRecall

/-!
# Equivalence-invariance of morphisms representable by algebraic spaces

Relative representability by algebraic spaces is invariant under 2-commutative
squares of 1-morphisms of groupoid fibrations over `(Sch/S)_fppf` whose
horizontal arrows are equivalences.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 94.9.3: let `S` be an object of `Sch_fppf`. Consider a 2-commutative
diagram of 1-morphisms of categories fibred in groupoids over `(Sch/S)_fppf`,
with horizontal arrows equivalences `eX : X' ≌ X` and `eY : Y' ≌ Y` and
vertical arrows `f : X ⟶ Y` and `f' : X' ⟶ Y'`. Then `f` is representable by
algebraic spaces if and only if `f'` is representable by algebraic spaces. -/
@[stacks 0457]
#check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.iff_of_equivalence :
    ∀ {S : Scheme.{u}} {X' X Y' Y : GroupoidsOver S}
    (eX : X' ≌ X) (eY : Y' ≌ Y) (f : X ⟶ Y) (f' : X' ⟶ Y')
    (sq : eX.hom ≫ f ≅ f' ≫ eY.hom),
    relativelyRepresentableByAlgebraicSpaces f ↔
      relativelyRepresentableByAlgebraicSpaces f')

end AlgebraicGeometry
