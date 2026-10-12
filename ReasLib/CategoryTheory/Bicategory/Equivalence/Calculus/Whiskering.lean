/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Equivalence.Calculus.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Whiskering by bicategorical equivalences

This leaf records that precomposition and postcomposition by equivalences
induce equivalences between the corresponding hom-categories.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

namespace Bicategory

variable {a b c d : B}

/-- Whiskering on the right by the forward morphism of a bicategorical equivalence induces an
equivalence of hom-categories. -/
instance precomp_isEquivalence (c : B) (e : a ≌ b) :
    Functor.IsEquivalence (precomp c e.hom) := sorry
/- Proof strategy: use `precomp c e.inv` as a quasi-inverse. Map the unit and counit of `e`
through precomposition, then combine them with the left unitor and associator natural
isomorphisms before applying `Functor.IsEquivalence.mk'`. -/

/-- Whiskering on the left by the forward morphism of a bicategorical equivalence induces an
equivalence of hom-categories. -/
instance postcomp_isEquivalence (a : B) (e : c ≌ d) :
    Functor.IsEquivalence (postcomp a e.hom) := sorry
/- Proof strategy: use `postcomp a e.inv` as a quasi-inverse. Map the unit and counit of `e`
through postcomposition, insert the right unitor and associator natural isomorphisms, and apply
`Functor.IsEquivalence.mk'`. -/

/-- Precomposition and postcomposition by bicategorical equivalences together induce an
equivalence between the corresponding hom-categories. -/
@[stacks 03YT "whiskering by equivalences induces a hom-category equivalence"]
theorem prePostcomp_isEquivalence (e₁ : a ≌ b) (e₂ : c ≌ d) :
    Functor.IsEquivalence
      (postcomp b e₂.hom ⋙ precomp d e₁.hom) := sorry
/- Proof strategy: use `precomp_isEquivalence` and `postcomp_isEquivalence`, followed by the
canonical instance that a composite of equivalences of categories is an equivalence. -/

end Bicategory

end CategoryTheory
