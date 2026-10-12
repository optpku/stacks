/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Bicategory.Strict.Basic
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

universe w v u

variable (B : Type u) [Bicategory.{w, v} B]

/-
nLab packages a strict `2`-category as a category enriched in `Cat`. Mathlib also supports that
presentation through `EnrichedCategory Cat`, but its conversion to the reusable bicategory API is
carried by the type synonym `CatEnriched`. The native surface for the rest of this chapter is
instead the pair `[Bicategory B] [Bicategory.Strict B]`: `Bicategory` owns the cells, vertical
composition, whiskering, and coherence, while `Bicategory.Strict` says that composition of
`1`-morphisms is strictly associative and unital and identifies the associator and unitors with
the corresponding equality transports.

This is equivalent to the source presentation at the intended mathematical level. Horizontal
composition is deliberately not repeated as primitive data here: mathlib derives it from the two
whiskerings and the exchange law. Likewise, `StrictBicategory.category` is a derived view on the
objects and `1`-morphisms, not another owner. Keeping only the two owner recalls therefore avoids
both a parallel strict-`2`-category structure and aliases for derived operations.
-/

/- Companion owner recall: `Bicategory B` supplies the objects, hom-categories, vertical
composition, horizontal whiskering, associator and unitors, and their coherence laws. -/
#check Bicategory

/- Definition 4.29.1: a strict `2`-category is canonically a type `B` with assumptions
`[Bicategory B] [Bicategory.Strict B]`. The first supplies the objects, `1`-morphisms,
hom-categories of `2`-morphisms, and horizontal composition; the second says that composition is
strictly associative and unital and that the bicategorical associator and unitors are the
corresponding equality-induced isomorphisms. -/
@[stacks 003H "strict 2-category as bicategory data with equality-induced associator and unitors"]
#check (Bicategory.Strict B : Prop)

end CategoryTheory
