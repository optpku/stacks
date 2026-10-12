/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.PositivePage
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Comparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Restricting spectral sequences to later pages

This file changes only the lower page bound of an existing spectral sequence.  It is useful when
comparing constructions that naturally begin on different pages, without adjoining artificial
earlier pages.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {κ : Type*} {c : ℤ → ComplexShape κ}

/-- Restrict a spectral sequence to the pages beginning at a later page. -/
@[stacks 011O "restriction to a later spectral-sequence page"]
abbrev fromPage {r₀ : ℤ} (E : SpectralSequence C c r₀) (r₁ : ℤ) (h : r₀ ≤ r₁) :
    SpectralSequence C c r₁ where
  page r hr := E.page r (h.trans hr)
  iso r r' pq hrr' hr := E.iso r r' pq hrr' (h.trans hr)

namespace FromPage

variable {r₀ r₁ : ℤ}

/-- Restrict a morphism of spectral sequences to the pages beginning at `r₁`. -/
@[stacks 011O "map after restricting to a later spectral-sequence page"]
abbrev map (h : r₀ ≤ r₁) {E E' : SpectralSequence C c r₀} (f : E ⟶ E') :
    fromPage E r₁ h ⟶ fromPage E' r₁ h where
  hom r hr := f.hom r (h.trans hr)
  comm r r' pq hrr' hr := f.comm r r' pq hrr' (h.trans hr)

/-- The page component of a later-page restriction is the original page component. -/
@[simp, stacks 011O "page-map computation after restricting to a later page"]
theorem map_hom (h : r₀ ≤ r₁) {E E' : SpectralSequence C c r₀} (f : E ⟶ E')
    (r : ℤ) (hr : r₁ ≤ r) :
    (map h f).hom r hr = f.hom r (h.trans hr) := sorry

/-- The entry component of a later-page restriction is the original entry component. -/
@[simp, stacks 011O "entry-map computation after restricting to a later page"]
theorem map_hom_f (h : r₀ ≤ r₁) {E E' : SpectralSequence C c r₀} (f : E ⟶ E')
    (r : ℤ) (hr : r₁ ≤ r) (pq : κ) :
    ((map h f).hom r hr).f pq = (f.hom r (h.trans hr)).f pq := sorry

/-- Restricting the identity spectral-sequence morphism gives the identity. -/
@[simp, stacks 011O "identity law for later-page restriction"]
theorem map_id (h : r₀ ≤ r₁) (E : SpectralSequence C c r₀) :
    map h (𝟙 E) = 𝟙 (fromPage E r₁ h) := sorry

/-- Restriction to later pages preserves composition of spectral-sequence morphisms. -/
@[simp, stacks 011O "composition law for later-page restriction"]
theorem map_comp (h : r₀ ≤ r₁) {E E' E'' : SpectralSequence C c r₀}
    (f : E ⟶ E') (g : E' ⟶ E'') :
    map h (f ≫ g) = map h f ≫ map h g := sorry

/-- Restriction to a fixed later page is a functor on spectral sequences. -/
@[stacks 011O "later-page restriction functor"]
def functor (h : r₀ ≤ r₁) :
    SpectralSequence C c r₀ ⥤ SpectralSequence C c r₁ where
  obj E := fromPage E r₁ h
  map f := map h f
  map_id E := map_id h E
  map_comp f g := map_comp h f g

namespace Functor

/-- The later-page restriction functor acts on objects by `fromPage`. -/
@[simp, stacks 011O "object computation for later-page restriction functor"]
theorem obj (h : r₀ ≤ r₁) (E : SpectralSequence C c r₀) :
    (functor h).obj E = fromPage E r₁ h := sorry

/-- The later-page restriction functor acts on morphisms by `FromPage.map`. -/
@[simp, stacks 011O "map computation for later-page restriction functor"]
theorem map (h : r₀ ≤ r₁) {E E' : SpectralSequence C c r₀} (f : E ⟶ E') :
    (functor h).map f = FromPage.map h f := sorry

end Functor

/-- An `IsIsoFrom` comparison remains an `IsIsoFrom` comparison after restricting the page bound. -/
@[stacks 011O "comparison transport under later-page restriction"]
theorem isIsoFrom (h : r₀ ≤ r₁) {r : ℤ} (hr : r₁ ≤ r)
    {E E' : SpectralSequence C c r₀} {f : E ⟶ E'}
    (hf : Hom.IsIsoFrom f r (h.trans hr)) :
    Hom.IsIsoFrom (map h f) r hr := sorry

end FromPage

namespace Page.Two

/-- Regard a spectral sequence beginning at page zero as one beginning at page two. -/
@[stacks 011O "page-two restriction"]
abbrev ofZero (E : SpectralSequence C c 0) : SpectralSequence C c 2 :=
  fromPage E 2 zero_le_two

end Page.Two

end CategoryTheory.SpectralSequence
