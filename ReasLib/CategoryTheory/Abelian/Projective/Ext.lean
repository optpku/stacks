/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.Projective.Characterizations
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.Data.List.TFAE

@[expose] public section

open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open CategoryTheory.Limits

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Tag 013C: an object is projective exactly when every degree-one extension out of it
vanishes.  This is the zero-element formulation of Mathlib's
`projective_iff_subsingleton_ext_one`. -/
@[stacks 013C]
theorem projective_iff_ext_one_eq_zero (P : C) :
    Projective P ↔ ∀ ⦃A : C⦄ (e : Ext P A 1), e = 0 := sorry

/-- Tag 013C: projectivity, exactness of the corepresented preadditive functor, splitting of short
exact sequences ending at the object, and vanishing of `Ext¹(P, -)` are equivalent. -/
@[stacks 013C]
theorem projective_tfae (P : C) :
    List.TFAE [
      Projective P,
      exactFunctor _ _ (preadditiveCoyonedaObj P),
      ∀ ⦃S : ShortComplex C⦄, S.X₃ = P → S.ShortExact → IsSplitEpi S.g,
      ∀ ⦃A : C⦄ (e : Ext P A 1), e = 0
    ] := sorry

end CategoryTheory
