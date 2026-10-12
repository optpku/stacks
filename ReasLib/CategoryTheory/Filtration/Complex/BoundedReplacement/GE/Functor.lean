/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.BoundedReplacement.GE

/-!
# Functorial lower truncation of filtered complexes

The universal descent map makes good lower truncation functorial.  This leaf keeps the map,
functor, projection natural transformation, and uniqueness API separate from the explicit
degreewise construction.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.TruncGE

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The map on good lower truncations induced by a filtered cochain map. -/
@[stacks 05S5 "functorial filtered lower truncation"]
noncomputable def map {K L : FilteredComplex A} (f : K ⟶ L) (a : ℤ) :
    truncGE K a ⟶ truncGE L a :=
  desc a (f ≫ πTruncGE L a) (isStrictlyGE L a)

/-- A component of the induced lower-truncation map is the corresponding descent component. -/
@[simp, stacks 05S5]
theorem map_f {K L : FilteredComplex A} (f : K ⟶ L) (a n : ℤ) :
    (map f a).f n =
      descComponent a (f ≫ πTruncGE L a) (isStrictlyGE L a) n := sorry

/-- The canonical lower-truncation projections are natural. -/
@[reassoc, stacks 05S5]
theorem π_naturality {K L : FilteredComplex A} (f : K ⟶ L) (a : ℤ) :
    πTruncGE K a ≫ map f a = f ≫ πTruncGE L a := sorry

/-- Lower truncation maps preserve identities. -/
@[simp]
theorem map_id (K : FilteredComplex A) (a : ℤ) :
    map (𝟙 K) a = 𝟙 (truncGE K a) := sorry

/-- Lower truncation maps preserve composition. -/
@[simp]
theorem map_comp {K L M : FilteredComplex A} (f : K ⟶ L) (g : L ⟶ M) (a : ℤ) :
    map (f ≫ g) a = map f a ≫ map g a := sorry

/-- Good lower truncation at a fixed cutoff is functorial. -/
@[stacks 05S5 "functorial filtered lower truncation"]
noncomputable def functor (a : ℤ) : FilteredComplex A ⥤ FilteredComplex A where
  obj K := truncGE K a
  map f := map f a
  map_id K := map_id K a
  map_comp f g := map_comp f g a

/-- Evaluating the lower-truncation functor gives good lower truncation. -/
@[simp, stacks 05S5]
theorem functor_obj (K : FilteredComplex A) (a : ℤ) :
    (functor (A := A) a).obj K = truncGE K a := sorry

/-- The lower-truncation functor acts on a morphism by the canonical descent map. -/
@[simp, stacks 05S5]
theorem functor_map {K L : FilteredComplex A} (f : K ⟶ L) (a : ℤ) :
    (functor (A := A) a).map f = map f a := sorry

namespace Projection

/-- Naturality of lower-truncation projections in the shape required by a natural
transformation. -/
@[stacks 05S5]
theorem naturality {K L : FilteredComplex A} (f : K ⟶ L) (a : ℤ) :
    (𝟭 (FilteredComplex A)).map f ≫ πTruncGE L a =
      πTruncGE K a ≫ (functor (A := A) a).map f := sorry

/-- The canonical projections form a natural transformation to good lower truncation. -/
@[stacks 05S5 "projection to functorial filtered lower truncation"]
noncomputable def natTrans (a : ℤ) :
    𝟭 (FilteredComplex A) ⟶ functor (A := A) a where
  app K := πTruncGE K a
  naturality := fun {K L} f ↦ naturality (A := A) (K := K) (L := L) f a

/-- A component of the projection natural transformation is the canonical truncation map. -/
@[simp, stacks 05S5]
theorem natTrans_app (K : FilteredComplex A) (a : ℤ) :
    (natTrans (A := A) a).app K = πTruncGE K a := sorry

end Projection

/-- Descent through lower truncation is uniquely determined by its composite with the canonical
projection. -/
@[stacks 05S5]
theorem desc_unique {K L : FilteredComplex A} (a : ℤ) (f : K ⟶ L)
    (hL : L.underlying.IsStrictlyGE a) (g : truncGE K a ⟶ L)
    (hg : πTruncGE K a ≫ g = f) : g = desc a f hL := sorry

/-- Two maps out of a lower truncation into a lower-bounded complex agree when their composites
with the canonical projection agree. -/
@[ext, stacks 05S5]
theorem hom_ext {K L : FilteredComplex A} (a : ℤ) (hL : L.underlying.IsStrictlyGE a)
    {f g : truncGE K a ⟶ L} (h : πTruncGE K a ≫ f = πTruncGE K a ≫ g) :
    f = g := sorry

/-- A map out of lower truncation is the canonical descent exactly when it has the prescribed
composite with the projection. -/
@[stacks 05S5]
theorem desc_eq_iff {K L : FilteredComplex A} (a : ℤ) (f : K ⟶ L)
    (hL : L.underlying.IsStrictlyGE a) (g : truncGE K a ⟶ L) :
    desc a f hL = g ↔ πTruncGE K a ≫ g = f := sorry

end CategoryTheory.FilteredComplex.TruncGE
