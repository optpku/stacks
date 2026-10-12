/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import ReasLib.Algebra.Category.ModuleCat.Ext.FlatBaseChange
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Epi descent for flat base change on Ext

These two diagram-lemma interfaces isolate the exact amount of degree-zero and degree-one
information needed to descend injectivity and surjectivity along an epimorphism.
@stack 05EG
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Abelian

universe u

namespace CategoryTheory.ModuleCat.Ext.FlatBaseChange

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Tag 05EG: injectivity of flat base change on `Ext¹` descends along an epimorphism when the
adjacent degree-zero base-change maps have the indicated one-sided properties. -/
@[stacks 05EG "injective Ext base change along an epimorphism"]
theorem map_injective_of_epi (f : R →+* S) {P M N : ModuleCat.{u} R}
    (p : P ⟶ M) [Epi p] (hf : f.Flat)
    (hP : Function.Injective (map f P N hf 1))
    (hHomP : Function.Surjective
      (fun g : P ⟶ N ↦ (ModuleCat.extendScalars f).map g))
    (hHomK : Function.Injective
      (fun g : kernel p ⟶ N ↦ (ModuleCat.extendScalars f).map g)) :
    Function.Injective (map f M N hf 1) := sorry

/-- Tag 05EG: surjectivity of flat base change on `Ext¹` descends along an epimorphism when the
kernel comparison is injective and the adjacent degree-zero comparison is surjective. -/
@[stacks 05EG "surjective Ext base change along an epimorphism"]
theorem map_surjective_of_epi (f : R →+* S) {P M N : ModuleCat.{u} R}
    (p : P ⟶ M) [Epi p] (hf : f.Flat)
    (hP : Function.Surjective (map f P N hf 1))
    (hK : Function.Injective (map f (kernel p) N hf 1))
    (hHomK : Function.Surjective
      (fun g : kernel p ⟶ N ↦ (ModuleCat.extendScalars f).map g)) :
    Function.Surjective (map f M N hf 1) := sorry

end CategoryTheory.ModuleCat.Ext.FlatBaseChange
