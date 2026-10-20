module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Stack
import StacksCheckRecall

/-!
# 2-fibre products with a stack along a representable morphism

If a 1-morphism of groupoid fibrations over `(Sch/S)_fppf` is representable by
algebraic spaces, then 2-fibre product against a stack in groupoids remains a
stack in groupoids.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 94.9.11: let `S` be a scheme contained in `Sch_fppf`. Let
`f : X ⟶ Z` and `g : Y ⟶ Z` be 1-morphisms of categories fibred in groupoids
over `(Sch/S)_fppf`. If `f` is representable by algebraic spaces and `Y` is a
stack in groupoids, then the 2-fibre product `TwoFibreProduct.apex f g` is a
stack in groupoids. -/
@[stacks 0CKY] #check
  (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.twoFibreProduct_isStack :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p],
    IsStack.InGroupoids (Scheme.fppfTopology.over S)
      (FiberedCategoryOver.Groupoids.p
        (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)))

/- If `f : X ⟶ Y` is representable by algebraic spaces and `Y` is a stack in
groupoids over `(Sch/S)_fppf`, then `X` is a stack in groupoids. -/
#check
  (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.source_isStack :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p],
    IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p)

end AlgebraicGeometry
