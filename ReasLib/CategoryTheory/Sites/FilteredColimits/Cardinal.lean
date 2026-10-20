module

public import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.FilteredColimits
public import ReasLib.CategoryTheory.Sites.Precoverage.Cardinality

/-!
# Cardinal-filtered colimits of sheaves

The finite and quasi-compact APIs in `Sites.FilteredColimits` address ordinary filtered
colimits.  This leaf owns the independent cardinal-filtered version, whose site hypothesis is
that covering presieves admit cardinally small generating families.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe wκ wI z v u

namespace CategoryTheory.Sites.FilteredColimitSections

variable {C : Type u} [Category.{v} C] {K : Coverage C}
variable {I : Type wI} [Category I]
variable {κ : Cardinal.{wκ}} [Fact κ.IsRegular] [IsCardinalFiltered I κ]
variable [HasWeakSheafify K.toGrothendieck (Type (max u v z))]

/-- A cardinal-filtered colimit of `Type`-valued sheaves is computed objectwise when every
covering presieve has raw arrow type of cardinality `< κ`.  The generating-family formulation is
available through `Precoverage.hasCardinalLTGeneratingFamilies_iff`; the two colimit assumptions
for sheaves and sections, together with the underlying presheaf colimit, are exactly the data
needed by the comparison construction. -/
theorem isIso_of_cardinalFiltered
    (F : I ⥤ Sheaf K.toGrothendieck (Type (max u v z))) (U : C)
    [HasColimit F]
    [HasColimit (F ⋙ (sheafSections K.toGrothendieck (Type (max u v z))).obj (op U))]
    [HasColimit (F ⋙ sheafToPresheaf K.toGrothendieck (Type (max u v z)))]
    (hK : K.hasCardinalLTCoveringPresieves κ) :
    IsIso (comparison F U) := sorry

end CategoryTheory.Sites.FilteredColimitSections
