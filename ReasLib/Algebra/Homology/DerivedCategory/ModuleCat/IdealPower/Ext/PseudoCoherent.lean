/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Noetherian.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Ext.Functor
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.Algebra.Module.IdealPower.Submodule
import Mathlib.Tactic.CrossRefAttribute

/-!
# Adic image bounds for derived Ext

For a pseudo-coherent derived source and a finite module target, the image of derived Ext from a
deep adic stage is contained in a predictably shallower adic stage of the ambient Ext module.
The restriction map, its pointwise bound, and eventual boundedness are separated so consumers can
reuse the conclusion without importing a chapter proof model.

@stack 0DYI
-/

@[expose] public section

open CategoryTheory
open Ideal.PowerSubmodule

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IdealPower.ExtImage

variable {A : Type u} [CommRing A]

/-- Derived Ext in the second variable applied to the inclusion of an adic stage. -/
@[stacks 0DYI "derived Ext map from an adic stage"]
noncomputable abbrev restriction
    (I : Ideal A) (K : DerivedCategory (ModuleCat A))
    (M : ModuleCat A) (p : ℤ) (n : ℕ) :
    (DerivedCategory.Ext.moduleFunctor K p).obj (stageObj I M n) ⟶
      (DerivedCategory.Ext.moduleFunctor K p).obj M :=
  (DerivedCategory.Ext.moduleFunctor K p).map ((subtypeNatTrans I n).app M)

/-- At cutoff `c` and stage `n`, the image of derived Ext restriction lies in adic stage
`n - c` of the ambient Ext module. -/
@[stacks 0DYI "adic image bound for derived Ext"]
def ImageBound
    (I : Ideal A) (K : DerivedCategory (ModuleCat A))
    (M : ModuleCat A) (p : ℤ) (c n : ℕ) : Prop :=
  LinearMap.range (restriction I K M p n).hom ≤
    stage I ((DerivedCategory.Ext.moduleFunctor K p).obj M) (n - c)

/-- One cutoff controls the image of all sufficiently deep derived Ext restrictions. -/
@[stacks 0DYI "eventual adic image bound for derived Ext"]
def EventuallyBounded
    (I : Ideal A) (K : DerivedCategory (ModuleCat A))
    (M : ModuleCat A) (p : ℤ) : Prop :=
  ∃ c : ℕ, ∀ n, c ≤ n → ImageBound I K M p c n

/-- Lemma 15.102.4 (0DYI): a pseudo-coherent derived source and a finite module target have an
eventual adic image bound in every integer Ext degree. -/
@[stacks 0DYI "Lemma 15.102.4"]
theorem eventuallyBounded_of_isPseudoCoherent
    [IsNoetherianRing A] (I : Ideal A)
    {K : DerivedCategory (ModuleCat A)} (hK : K.IsPseudoCoherent)
    (M : ModuleCat A) [Module.Finite A M] (p : ℤ) :
    EventuallyBounded I K M p := sorry

end CategoryTheory.DerivedCategory.IdealPower.ExtImage
