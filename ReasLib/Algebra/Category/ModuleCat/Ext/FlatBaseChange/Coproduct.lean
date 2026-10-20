module

public import ReasLib.Algebra.Category.ModuleCat.Ext.FlatBaseChange
public import ReasLib.Algebra.Homology.DerivedCategory.Ext.Coproduct
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat base change on Ext and coproducts

This leaf turns the canonical coproduct decomposition of Ext into a componentwise criterion for
the flat base-change map.
@stack 05EG
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace CategoryTheory.ModuleCat.Ext.FlatBaseChange

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Tag 05EG: if flat base change is bijective on every summand, it is bijective on their module
coproduct. -/
@[stacks 05EG "flat base change on Ext over coproducts"]
theorem map_coproduct_bijective {ι : Type u}
    (f : R →+* S) (X : ι → ModuleCat.{u} R) (N : ModuleCat.{u} R)
    (hf : f.Flat) (i : ℕ)
    (hX : ∀ j, Function.Bijective (map f (X j) N hf i)) :
    Function.Bijective (map f (∐ X) N hf i) := sorry

end CategoryTheory.ModuleCat.Ext.FlatBaseChange
