/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Resolution
public import ReasLib.CategoryTheory.DisplayedCategory.Transport

/-!
# Displayed category of finite filtered-injective resolutions

This leaf packages strict filtered-injective resolutions and their dependent maps as a displayed
category over bounded-below complexes of finite filtered objects.  The concrete identity and
composition owners remain in `Resolution.Map`; this file supplies only the neutral displayed
packaging and its equality-transport bridge.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredInjectivePlus.Resolution

/-- The displayed category of strict filtered-injective resolutions over finite filtered
complexes. -/
@[stacks 05TU "displayed category of finite filtered-injective resolutions"]
noncomputable def displayedCategory (C : Type u) [Category.{v} C] [Abelian C] :
    DisplayedCategory (CochainComplex.Plus (FilteredObject.Finite.category C)) where
  obj := Resolution
  Hom := fun f R S => Map f R S
  id := Map.id
  comp := Map.comp
  id_comp := fun _ => sorry
  comp_id := fun _ => sorry
  assoc := fun _ _ _ => sorry

/-- The displayed-object family of strict filtered-injective resolutions. -/
@[simp]
theorem displayedCategory_obj
    (K : CochainComplex.Plus (FilteredObject.Finite.category C)) :
    (displayedCategory C).obj K = Resolution K := rfl

/-- The displayed hom family of strict filtered-injective resolution maps. -/
@[simp]
theorem displayedCategory_hom
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    (R : Resolution K) (S : Resolution L) :
    (displayedCategory C).Hom f R S = Map f R S := rfl

/-- The identity operation of the displayed strict-resolution category. -/
@[simp]
theorem displayedCategory_id
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)} (R : Resolution K) :
    (displayedCategory C).id R = Map.id R := rfl

/-- The composition operation of the displayed strict-resolution category. -/
@[simp]
theorem displayedCategory_comp
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category C)}
    {f : K ⟶ L} {g : L ⟶ M} {R : Resolution K} {S : Resolution L} {T : Resolution M}
    (m : Map f R S) (n : Map g S T) :
    (displayedCategory C).comp m n = Map.comp m n := rfl

/-- Custom reindexing of a strict filtered-injective resolution map agrees with canonical
displayed hom transport. -/
@[simp, stacks 05TU "transport of finite filtered-injective resolution maps"]
theorem Map.reindex_eq_cast
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f g : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (h : f = g) (m : Map f R S) :
    Map.reindex h m =
      DisplayedCategory.Hom.cast (displayedCategory C) h m := sorry

/-- The generic displayed transport can be converted back to the owner-level strict-resolution
reindexing. -/
@[stacks 05TU "owner-level transport of finite filtered-injective resolution maps"]
theorem Map.cast_eq_reindex
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f g : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (h : f = g) (m : Map f R S) :
    DisplayedCategory.Hom.cast (displayedCategory C) h m = Map.reindex h m :=
  (Map.reindex_eq_cast h m).symm

end FilteredInjectivePlus.Resolution

end CochainComplex
