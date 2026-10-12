/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Under.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.Flat.FilteredColimit

/-!
# Faithfully flat maps and filtered colimits

This leaf owns the fixed-base filtered-colimit theorem for faithfully flat
commutative algebras. The base ring is represented by the under-category
`Under (CommRingCat.of R)`, the canonical categorical model of an `R`-algebra
in this setting.

The stagewise hypotheses are explicit rather than typeclass parameters:
faithful flatness is a mathematical premise of the theorem, not a canonical
instance that should be synthesized for every stage of an arbitrary diagram.
We also do not register a global
`MorphismProperty.IsStableUnderFilteredColimits` instance: the fixed-base
theorem is the justified abstraction exposed by the source result, while a
varying-source arrow-category theorem would require additional hypotheses and
a separate API decision.
-/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.Under
open CommRingCat CommRingCat.Hom

universe u v

namespace RingHom.FaithfullyFlat

/-- Lemma 10.39.20, tag `090N`: a filtered colimit cocone of faithfully flat
commutative `R`-algebras is faithfully flat over `R`. -/
@[stacks 090N "fixed-base filtered-colimit closure"]
theorem of_isColimit_under
    {R : Type u} [CommRing R]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of R))
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, (hom (F.obj j).hom).FaithfullyFlat) :
    (hom c.pt.hom).FaithfullyFlat := sorry

/-- The canonical-colimit specialization of `of_isColimit_under`. -/
theorem of_colimit_under
    {R : Type u} [CommRing R]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of R)) [HasColimit F]
    (hF : ∀ j, (hom (F.obj j).hom).FaithfullyFlat) :
    (hom (colimit F).hom).FaithfullyFlat := sorry

end RingHom.FaithfullyFlat
