module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ext and arbitrary coproducts

The canonical map is written explicitly by precomposition with the coproduct injections.  The
bijectivity statement is kept as a proposition so downstream code can choose the appropriate
equivalence without hiding a noncanonical inverse in the shared API.
@stack 05EG
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Abelian

universe u

namespace CategoryTheory.ModuleCat.Ext

variable {R : Type u} [CommRing R]

/-- Tag 05EG: first-variable Ext over an arbitrary module coproduct is detected by its canonical
precomposition map to the family of Ext groups of the summands. -/
@[stacks 05EG "Ext over arbitrary module coproducts"]
theorem coproduct_precomp_bijective {ι : Type u}
    (X : ι → ModuleCat.{u} R) (N : ModuleCat.{u} R) (i : ℕ) :
    Function.Bijective
      (fun e : Ext (∐ X) N i => fun j ↦
        (Ext.mk₀ (Sigma.ι X j)).comp e (zero_add i)) := sorry

end CategoryTheory.ModuleCat.Ext
