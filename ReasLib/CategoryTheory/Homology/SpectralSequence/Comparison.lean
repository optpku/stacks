module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Comparison Properties of Spectral Sequences

This module records representation-independent properties of morphisms of spectral sequences.
They apply to arbitrary page shapes and starting pages, independently of any construction of a
spectral sequence.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace SpectralSequence.Hom

variable {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}

/-- A morphism of spectral sequences is an isomorphism from page `r` onward when every entry of
every defined page at least `r` is mapped isomorphically.  The single proof `hr` records that
the initial page belongs to the spectral sequence, so consumers do not repeat lower-bound proofs
at every later page. -/
@[stacks 011O "isomorphism from a spectral-sequence page onward"]
def IsIsoFrom {E E' : SpectralSequence C c r₀} (f : E ⟶ E')
    (r : ℤ) (hr : r₀ ≤ r) : Prop :=
  ∀ (s : ℤ) (hrs : r ≤ s) (pq : κ),
    IsIso ((f.hom s (hr.trans hrs)).f pq)

/-- An `IsIsoFrom` hypothesis supplies an isomorphism on each entry of every later page. -/
theorem IsIsoFrom.isIso {E E' : SpectralSequence C c r₀} {f : E ⟶ E'}
    {r : ℤ} {hr : r₀ ≤ r} (h : IsIsoFrom f r hr)
    (s : ℤ) (hrs : r ≤ s) (pq : κ) :
    IsIso ((f.hom s (hr.trans hrs)).f pq) := sorry

/-- It suffices to test `IsIsoFrom` on the entries of its initial page.  Compatibility with
successive-page homology propagates those isomorphisms to every later page. -/
@[stacks 011O "initial-page criterion for a spectral-sequence comparison"]
theorem isIsoFrom_iff {E E' : SpectralSequence C c r₀} (f : E ⟶ E')
    (r : ℤ) (hr : r₀ ≤ r) :
    IsIsoFrom f r hr ↔ ∀ pq : κ, IsIso ((f.hom r hr).f pq) := sorry

/-- An `IsIsoFrom` comparison can equivalently be checked on the bundled map of its initial
page.  This is the convenient interface when the page map is already known to be an isomorphism. -/
@[stacks 011O "bundled initial-page criterion for a spectral-sequence comparison"]
theorem isIsoFrom_iff_isIso_hom {E E' : SpectralSequence C c r₀} (f : E ⟶ E')
    (r : ℤ) (hr : r₀ ≤ r) :
    IsIsoFrom f r hr ↔ IsIso (f.hom r hr) := sorry

/-- Entrywise isomorphisms on one page determine an isomorphism from that page onward. -/
@[stacks 011O "spectral-sequence comparison from an initial page"]
theorem IsIsoFrom.of_page {E E' : SpectralSequence C c r₀} {f : E ⟶ E'}
    {r : ℤ} {hr : r₀ ≤ r}
    (h : ∀ pq : κ, IsIso ((f.hom r hr).f pq)) :
    IsIsoFrom f r hr := sorry

/-- A bundled isomorphism on the initial page gives an isomorphism from that page onward. -/
@[stacks 011O "spectral-sequence comparison from a bundled page isomorphism"]
theorem IsIsoFrom.of_page_isIso {E E' : SpectralSequence C c r₀} {f : E ⟶ E'}
    {r : ℤ} {hr : r₀ ≤ r} [IsIso (f.hom r hr)] :
    IsIsoFrom f r hr := sorry

/-- Every bundled page map on or after the comparison threshold is an isomorphism. -/
@[stacks 011O "page isomorphism from a spectral-sequence comparison"]
theorem IsIsoFrom.hom_isIso {E E' : SpectralSequence C c r₀} {f : E ⟶ E'}
    {r : ℤ} {hr : r₀ ≤ r} (h : IsIsoFrom f r hr)
    (s : ℤ) (hrs : r ≤ s) :
    IsIso (f.hom s (hr.trans hrs)) := sorry

/-- Being an isomorphism from a page onward persists after increasing the initial page. -/
theorem IsIsoFrom.mono {E E' : SpectralSequence C c r₀} {f : E ⟶ E'}
    {r s : ℤ} {hr : r₀ ≤ r} {hs : r₀ ≤ s}
    (h : IsIsoFrom f r hr) (hrs : r ≤ s) :
    IsIsoFrom f s hs := sorry

/-- The identity morphism is an isomorphism from every defined page onward. -/
@[stacks 011O "identity spectral-sequence comparison"]
theorem isIsoFrom_id (E : SpectralSequence C c r₀) (r : ℤ) (hr : r₀ ≤ r) :
    IsIsoFrom (𝟙 E) r hr := sorry

/-- Isomorphisms from a page onward are closed under composition. -/
@[stacks 011O "composition of spectral-sequence comparisons"]
theorem IsIsoFrom.comp
    {E E' E'' : SpectralSequence C c r₀} {f : E ⟶ E'} {g : E' ⟶ E''}
    {r : ℤ} {hr : r₀ ≤ r}
    (hf : IsIsoFrom f r hr) (hg : IsIsoFrom g r hr) :
    IsIsoFrom (f ≫ g) r hr := sorry

/-- Composing on the left with an `IsIsoFrom` comparison does not change whether the other
factor is an isomorphism from the same page onward. -/
@[stacks 011O "left cancellation for spectral-sequence comparisons"]
theorem isIsoFrom_comp_left_iff
    {E E' E'' : SpectralSequence C c r₀} (f : E ⟶ E') (g : E' ⟶ E'')
    {r : ℤ} {hr : r₀ ≤ r} (hf : IsIsoFrom f r hr) :
    IsIsoFrom (f ≫ g) r hr ↔ IsIsoFrom g r hr := sorry

/-- Composing on the right with an `IsIsoFrom` comparison does not change whether the other
factor is an isomorphism from the same page onward. -/
@[stacks 011O "right cancellation for spectral-sequence comparisons"]
theorem isIsoFrom_comp_right_iff
    {E E' E'' : SpectralSequence C c r₀} (f : E ⟶ E') (g : E' ⟶ E'')
    {r : ℤ} {hr : r₀ ≤ r} (hg : IsIsoFrom g r hr) :
    IsIsoFrom (f ≫ g) r hr ↔ IsIsoFrom f r hr := sorry

/-- A categorical isomorphism of spectral sequences is an isomorphism from every defined page
onward. -/
@[stacks 011O "comparison induced by a spectral-sequence isomorphism"]
theorem isIsoFrom_of_isIso
    {E E' : SpectralSequence C c r₀} (f : E ⟶ E') [IsIso f]
    (r : ℤ) (hr : r₀ ≤ r) : IsIsoFrom f r hr := sorry

end SpectralSequence.Hom

end CategoryTheory
