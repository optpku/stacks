module

public import ReasLib.CategoryTheory.Filtration.Complex.PageOne

/-!
# Isomorphism transport for the boundary-model first page

The page-one map and its bidegree components inherit isomorphism status from an isomorphism of
filtered complexes.  Keeping these instances in a small leaf makes spectral-sequence transport
available without importing additive or convergence layers.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.Page.One

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Every bidegree component of a boundary-model first-page map is an isomorphism when the
filtered-complex map is. -/
@[stacks 012N "isomorphism on boundary-model first-page components"]
noncomputable instance mapComponent_isIso {K L : FilteredComplex C} (f : K ⟶ L)
    (pq : ℤ × ℤ) [IsIso f] : IsIso (mapComponent f pq) := sorry

/-- A boundary-model first-page map is an isomorphism when its filtered-complex map is. -/
@[stacks 012N "isomorphism of boundary-model first-page maps"]
noncomputable instance map_isIso {K L : FilteredComplex C} (f : K ⟶ L)
    [IsIso f] : IsIso (map f) := sorry

variable {K L : FilteredComplex C} (f : K ⟶ L) [IsIso f]
#synth IsIso (map f)
#synth IsIso (mapComponent f (0, 0))

end CategoryTheory.FilteredComplex.Page.One
