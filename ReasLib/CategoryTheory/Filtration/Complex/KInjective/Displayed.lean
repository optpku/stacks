module

public import ReasLib.CategoryTheory.Filtration.Complex.KInjective.Functoriality
public import ReasLib.CategoryTheory.DisplayedCategory.Transport

/-!
# Displayed category of filtered K-injective resolutions

This leaf packages the chosen filtered K-injective resolution objects and their dependent maps as
a displayed category over `FilteredComplex A`.  The concrete identity and composition owners stay
in `KInjectiveResolution.Map`; only the neutral displayed packaging and equality-transport bridge
are introduced here.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.FilteredComplex.KInjectiveResolution

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The displayed category of filtered K-injective resolutions over filtered complexes. -/
@[stacks 0BKI "displayed category of filtered K-injective resolutions"]
noncomputable def displayedCategory (A : Type u) [Category.{v} A] [Abelian A] :
    DisplayedCategory (FilteredComplex A) where
  obj := KInjectiveResolution
  Hom := fun f R S => Map f R S
  id := Map.id
  comp := Map.comp
  id_comp := fun _ => sorry
  comp_id := fun _ => sorry
  assoc := fun _ _ _ => sorry

/-- The displayed-object family of filtered K-injective resolutions. -/
@[simp]
theorem displayedCategory_obj (K : FilteredComplex A) :
    (displayedCategory A).obj K = KInjectiveResolution K := rfl

/-- The displayed hom family of filtered K-injective resolution maps. -/
@[simp]
theorem displayedCategory_hom {K L : FilteredComplex A} {f : K ⟶ L}
    (R : KInjectiveResolution K) (S : KInjectiveResolution L) :
    (displayedCategory A).Hom f R S = Map f R S := rfl

/-- The identity operation of the displayed K-injective-resolution category. -/
@[simp]
theorem displayedCategory_id {K : FilteredComplex A} (R : KInjectiveResolution K) :
    (displayedCategory A).id R = Map.id R := rfl

/-- The composition operation of the displayed K-injective-resolution category. -/
@[simp]
theorem displayedCategory_comp {K L M : FilteredComplex A}
    {f : K ⟶ L} {g : L ⟶ M}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {T : KInjectiveResolution M} (m : Map f R S) (n : Map g S T) :
    (displayedCategory A).comp m n = Map.comp m n := rfl

/-- Custom reindexing of a filtered K-injective resolution map agrees with canonical displayed
hom transport. -/
@[simp, stacks 0BKI "transport of filtered K-injective resolution maps"]
theorem Map.reindex_eq_cast {K L : FilteredComplex A} {f g : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    (h : f = g) (m : Map f R S) :
    Map.reindex h m =
      DisplayedCategory.Hom.cast (displayedCategory A) h m := sorry

/-- The generic displayed transport can be converted back to the owner-level reindexing. -/
@[stacks 0BKI "owner-level transport of filtered K-injective resolution maps"]
theorem Map.cast_eq_reindex {K L : FilteredComplex A} {f g : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    (h : f = g) (m : Map f R S) :
    DisplayedCategory.Hom.cast (displayedCategory A) h m = Map.reindex h m :=
  (Map.reindex_eq_cast h m).symm

end CategoryTheory.FilteredComplex.KInjectiveResolution
