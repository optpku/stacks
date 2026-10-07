module

public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Base change of a representable-by-spaces morphism along a space

If a 1-morphism of groupoid fibrations over `(Sch/S)_fppf` is representable by
algebraic spaces and the second leg is representable by an algebraic space, then
the 2-fibre product is representable by an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Lemma 94.9.8: let `S` be an object of `Sch_fppf`. Let `X`, `Y`, `Z` be
categories fibred in groupoids over `(Sch/S)_fppf`. If `f : X ⟶ Y` is a
1-morphism representable by algebraic spaces and `Z` is representable by an
algebraic space over `S`, then the 2-fibre product `TwoFibreProduct.apex g f`
is representable by an algebraic space. -/
@[stacks 0300]
theorem IsRepresentableByAlgebraicSpace.twoFibreProduct
    {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    (hZ : IsRepresentableByAlgebraicSpace Z) :
    IsRepresentableByAlgebraicSpace
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f) := sorry

/-- The 2-fibre product of a morphism representable by algebraic spaces against a
groupoid fibration representable by an algebraic space is equivalent to the
groupoid fibration of some algebraic space over `S`. -/
theorem IsRepresentableByAlgebraicSpace.exists_twoFibreProduct
    {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    (hZ : IsRepresentableByAlgebraicSpace Z) :
    ∃ F : AlgebraicSpace S,
      Nonempty (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f ≌ F.toGroupoids) :=
  sorry

/-- If `f : X ⟶ Y` is representable by algebraic spaces, then the 2-fibre product
of `G.toGroupoids ⟶ Y` against `f` is representable by an algebraic space. -/
theorem IsRepresentableByAlgebraicSpace.twoFibreProduct_of_toGroupoids
    {S : Scheme.{u}} {X Y : GroupoidsOver S} {G : AlgebraicSpace S}
    (f : X ⟶ Y) (g : G.toGroupoids ⟶ Y)
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    IsRepresentableByAlgebraicSpace
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f) := sorry

end AlgebraicGeometry
