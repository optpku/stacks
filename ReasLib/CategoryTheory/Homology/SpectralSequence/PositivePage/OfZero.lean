/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.PositivePage
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functorial page-one views of zero-based spectral sequences

Forgetting the zeroth page acts on spectral-sequence morphisms as well as objects.  This file owns
that generic map and functor, together with the component, identity, and composition computations
needed by renumbering constructions.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.SpectralSequence.Page.One

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {κ : Type*} {c : ℤ → ComplexShape κ}

/-- Forgetting the zeroth page of a spectral-sequence morphism. -/
@[stacks 0BDU "page-one view of a zero-based spectral-sequence map"]
abbrev map {E E' : SpectralSequence C c 0} (f : E ⟶ E') :
    ofZero E ⟶ ofZero E' where
  hom r hr := f.hom r (zero_le_one.trans hr)
  comm r r' pq hrr' hr := f.comm r r' pq hrr' (zero_le_one.trans hr)

/-- Forgetting the zeroth page retains the original map on every positive page. -/
@[simp, stacks 0BDU "page-map computation for the page-one view"]
theorem map_hom {E E' : SpectralSequence C c 0} (f : E ⟶ E')
    (r : ℤ) (hr : 1 ≤ r) :
    (map f).hom r hr = f.hom r (zero_le_one.trans hr) := sorry

/-- A page-one view computes componentwise by the original page map. -/
@[simp, stacks 0BDU "component computation for the page-one view"]
theorem map_hom_f {E E' : SpectralSequence C c 0} (f : E ⟶ E')
    (r : ℤ) (hr : 1 ≤ r) (i : κ) :
    ((map f).hom r hr).f i = (f.hom r (zero_le_one.trans hr)).f i := sorry

/-- Forgetting the zeroth page preserves identity maps. -/
@[simp, stacks 0BDU "identity law for the page-one view"]
theorem map_id (E : SpectralSequence C c 0) :
    map (𝟙 E) = 𝟙 (ofZero E) := sorry

/-- Forgetting the zeroth page preserves composition of spectral-sequence maps. -/
@[simp, stacks 0BDU "composition law for the page-one view"]
theorem map_comp {E E' E'' : SpectralSequence C c 0}
    (f : E ⟶ E') (g : E' ⟶ E'') :
    map (f ≫ g) = map f ≫ map g := sorry

/-- Forgetting the zeroth page is a functor on spectral sequences. -/
@[stacks 0BDU "page-one view functor"]
def functor (c : ℤ → ComplexShape κ) :
    SpectralSequence C c 0 ⥤ SpectralSequence C c 1 where
  obj E := ofZero E
  map f := map f
  map_id E := map_id E
  map_comp f g := map_comp f g

namespace Functor

/-- The page-one view functor acts on objects by `Page.One.ofZero`. -/
@[simp, stacks 0BDU "object computation for the page-one view functor"]
theorem obj (c : ℤ → ComplexShape κ) (E : SpectralSequence C c 0) :
    (functor (C := C) c).obj E = ofZero E := sorry

/-- The page-one view functor acts on morphisms by `Page.One.map`. -/
@[simp, stacks 0BDU "map computation for the page-one view functor"]
theorem map (c : ℤ → ComplexShape κ) {E E' : SpectralSequence C c 0}
    (f : E ⟶ E') :
    (functor (C := C) c).map f = Page.One.map f := sorry

end Functor

end CategoryTheory.SpectralSequence.Page.One
